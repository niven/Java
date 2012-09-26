

import java.util.ArrayList;
import java.util.BitSet;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Random;
import java.util.Set;
import java.util.TreeSet;

public class BipartiteCover {

	private static final int TEAM_COUNT = 10 * 1000;
	private static final int EMPLOYEE_COUNT = 1000; // per side

	/**
	 * @param args
	 * @throws MalformedURLException
	 * @throws URISyntaxException
	 */
	public static void main(String[] args) {

		Map<Integer, Team> teams = make_teams();

		// System.out.println( teams );
		long start = System.currentTimeMillis();
		System.out.println("Partitioning into disjoint subsets of teams");
		List<Set<Integer>> partitions = partition( teams );
		List<Cover> minimals = new ArrayList<Cover>();
		BitSet solution = new BitSet(); // employees
		for(Set<Integer> subset : partitions) {
			System.out.println( "Finding cover for " + subset.size() + " teams" );
			Cover minimal = find_minimal_cover( subset, teams );
			minimals.add( minimal );
			System.out.println( "Subsolution: (" + minimal.empl.cardinality() + " employees) " + minimal );
			solution.or( minimal.empl );
		}

		System.out.println( "milliseconds: " + (System.currentTimeMillis() - start) );
		System.out.println( "Solution: " + solution.cardinality() + " employees:\n" + solution );

		System.out.println( "Correct: " + check( solution, teams ) );
	}

	/**
	 * Check if our solution is correct (all teams covered)
	 * 
	 * @param solution
	 * @param teams
	 * @return
	 */
	private static boolean check(BitSet solution, Map<Integer, Team> teams) {

		for(Team t : teams.values()) {
			if( !(solution.get( t.a ) || solution.get( t.b )) ) {
				return false;
			}
		}

		return true;
	}

	// break up into disjoint sets
	// this really cuts back on the work when you have teams_count ~= employee_count
	private static List<Set<Integer>> partition(Map<Integer, Team> teams) {

		List<Integer> pending = new ArrayList<Integer>( teams.keySet() );

		Map<Integer, List<Integer>> empl_teams = employees_to_teams( teams );

		List<Set<Integer>> subsets = new ArrayList<Set<Integer>>();
		while( pending.size() > 0 ) {

			int team_id = pending.remove( 0 );
			Set<Integer> all = new HashSet<Integer>();
			all.add( team_id );
			// now keep adding teams as long as we can reach them through employees
			List<Integer> todo = new ArrayList<Integer>();
			todo.add( team_id );
			while( todo.size() > 0 ) {
				Team team = teams.get( todo.remove( 0 ) );

				// get teams we can reach with these employees
				List<Integer> a_teams = empl_teams.get( team.a );
				List<Integer> b_teams = empl_teams.get( team.b );

				// remove teams we already have
				a_teams.removeAll( all );
				b_teams.removeAll( all );

				// add them to reachable teams
				all.addAll( a_teams );
				all.addAll( b_teams );

				// add them to the todo list: they might enable us to reach more teams
				todo.addAll( a_teams );
				todo.addAll( b_teams );

			}
			// remove teams we got from the pending list
			pending.removeAll( all );

			subsets.add( all );
		}
		return subsets;
	}

	/**
	 * Map from employee to all teams they can reach
	 * 
	 * @param teams
	 * @return
	 */
	private static Map<Integer, List<Integer>> employees_to_teams(Map<Integer, Team> teams) {

		Map<Integer, List<Integer>> e2t = new HashMap<Integer, List<Integer>>();

		for(Entry<Integer, Team> e : teams.entrySet()) {
			Integer team_id = e.getKey();
			Team team = e.getValue();

			List<Integer> e_teams = e2t.containsKey( team.a ) ? e2t.get( team.a ) : new ArrayList<Integer>();
			e_teams.add( team_id );
			e2t.put( team.a, e_teams );

			e_teams = e2t.containsKey( team.b ) ? e2t.get( team.b ) : new ArrayList<Integer>();
			e_teams.add( team_id );
			e2t.put( team.b, e_teams );
		}

		return e2t;
	}

	private static Comparator<Cover> empl_asc_reachable_desc = new Comparator<Cover>() {

		@Override
		public int compare(Cover o1, Cover o2) {
			return o1.empl.size() == o2.empl.size() ? (o1.unreachable_teams.cardinality() == o2.unreachable_teams.cardinality() ?
			/* just to ensure 2 objects are never equal, but always have total order */
			o1.hashCode() - o2.hashCode() : o1.unreachable_teams.cardinality() - o2.unreachable_teams.cardinality()) : o1.empl.size() - o2.empl.size();
		}
	};

	private static Cover find_minimal_cover(Set<Integer> subteam, Map<Integer, Team> all_teams) {

		Map<Integer, Team> teams = new HashMap<Integer, Team>();
		for(int team_id : subteam) {
			teams.put( team_id, all_teams.get( team_id ) );
		}

		// turn all teams into covers
		TreeSet<Cover> covers = new TreeSet<Cover>( empl_asc_reachable_desc ); // sorted by most teams reached first

		for(Entry<Integer, Team> t : teams.entrySet()) {
			Cover ca = new Cover( t.getValue().a );
			Cover cb = new Cover( t.getValue().b );
			for(Entry<Integer, Team> t2 : teams.entrySet()) {
				if( t2.getKey() != t.getKey() ) {
					ca.unreachable_teams.set( t2.getKey() );
					cb.unreachable_teams.set( t2.getKey() );
				}
			}
			expand( ca, teams );
			expand( cb, teams );
			if( ca.unreachable_teams.isEmpty() ) {
				return ca;
			}
			if( cb.unreachable_teams.isEmpty() ) {
				return cb;
			}
			covers.add( ca );
			covers.add( cb );

		}

		while( true ) {
			// take cover that reaches most teams, with least employees (greedy)
			Cover c = covers.first();
			covers.remove( c );

			// make 2 covers for each cover by adding a team (branch the cover path)
			int team_id = c.unreachable_teams.nextSetBit( 0 ); // if none left we would have exited already
			Team t = teams.get( team_id );

			// for both:
			// add all teams they can now reach
			Cover left = c.copy();
			left.empl.set( t.a );
			left.unreachable_teams.set( team_id );
			expand( left, teams );
			if( left.unreachable_teams.isEmpty() ) {
				return left;
			}
			covers.add( left );

			Cover right = c.copy();
			right.empl.set( t.b );
			right.unreachable_teams.set( team_id );
			expand( right, teams );

			if( right.unreachable_teams.isEmpty() ) {
				return right;
			}
			covers.add( right );
		}
	}

	// add all teams this cover can reach
	private static void expand(Cover c, Map<Integer, Team> teams) {

		for(Entry<Integer, Team> t : teams.entrySet()) {
			if( t.getValue().hasMember( c.empl ) ) {
				c.unreachable_teams.clear( t.getKey() );
			}
		}

	}

	/**
	 * Make up teams of random (unique) combinations of employees
	 * 
	 * @return
	 */
	private static Map<Integer, Team> make_teams() {

		int[] a_employees = new int[EMPLOYEE_COUNT]; // IDs
		int[] b_employees = new int[EMPLOYEE_COUNT]; // IDs
		for(int i = 0; i < EMPLOYEE_COUNT; i++) {
			a_employees[i] = i;
			b_employees[i] = EMPLOYEE_COUNT + i;
		}

		Random rand = new Random();
		Map<Integer, Team> teams = new HashMap<Integer, Team>( TEAM_COUNT );

		int tId = 0;
		for(int i = 0; i < TEAM_COUNT; i++) {
			int a = a_employees[rand.nextInt( EMPLOYEE_COUNT )];
			int b = b_employees[rand.nextInt( EMPLOYEE_COUNT )];
			Team team = new Team( a, b );
			// guarantee unique teams
			while( teams.values().contains( team ) ) {
				a = a_employees[rand.nextInt( EMPLOYEE_COUNT )];
				b = b_employees[rand.nextInt( EMPLOYEE_COUNT )];
				team = new Team( a, b );
			}

			teams.put( tId++, team );
		}

		return teams;
	}

	private static class Cover {

		public Cover(int a) {
			empl.set( a );
		}

		private Cover() {// for copy
		}

		public Cover copy() {
			Cover c = new Cover();
			c.empl.or( empl );
			c.unreachable_teams.or( unreachable_teams );
			return c;
		}

		public BitSet unreachable_teams = new BitSet( TEAM_COUNT );
		public BitSet empl = new BitSet( EMPLOYEE_COUNT * 2 ); // fit both a and b employees

		@Override
		public String toString() {
			return empl.toString() + ": unreachable: " + unreachable_teams.toString();
		}
	}

	private static class Team {
		int a;
		int b;

		public Team(int a, int b) {
			this.a = a;
			this.b = b;
		}

		public boolean hasMember(BitSet empl) {
			return empl.get( a ) || empl.get( b );
		}

		@Override
		public String toString() {
			return a + " - " + b;
		}

	}

}
