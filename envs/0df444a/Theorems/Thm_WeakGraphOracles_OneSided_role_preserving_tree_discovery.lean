-- Prove2me | Theorems.Thm_WeakGraphOracles_OneSided_role_preserving_tree_discovery
-- name    : WeakGraphOracles.OneSided.role_preserving_tree_discovery
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:22:41.744728+00:00
-- url     : https://prove2.me/theorems/36e40216-cfa5-4221-aa76-e6147d6e8c66
-- title:
--   Theorem 7 — tree discovery with explicit probability and query bound
-- statement:
--   Let $T$ be a fixed tree with $k\ge1$ edges. Set $h=2k$, $s=\lceil4h\log h\rceil$, and $Q=1+ks(s+1)^k$. For each $n$ there is one GEN1 policy of worst-run depth at most $Q$ working on every graph $G$ whose entire edge set is the union of a nonempty, edge-disjoint, role-preserving collection of $T$-appearances. Its observed edges contain a $T$-appearance with probability
--
--   $$\Pr[\text{discover }T]\ge1-k(2k)^{-8}\ge\frac23.$$
--
--   The policy is fixed before $G$; the role map and collection occur only in the mathematical setup. The bound depends on $T$ and is independent of $n$. This is the reduced-graph discovery theorem used to obtain the singleton tester; arbitrary inputs to the goal are not required to have this structure.
--
--   Differences from the source:
--   - encoding: finite simple graphs with labels [n] → SimpleGraph (Fin n), with finite patterns carrying their own order; reason: relabeling by the standard bijection preserves every graph, appearance, degree and edge count
--   - encoding: adaptive randomized algorithms with at most q oracle queries → PMF over complete deterministic query plans of depth at most q, executed against fresh uniform response kernels; reason: finite query and reply alphabets at each fixed n and q make this equivalent to arbitrary internal randomization; no hidden graph is supplied to a policy
--   - encoding: s=4h log h random-neighbor queries per discovered vertex, h=2k → s is the natural-number ceiling of 4h log h, with query bound 1+k*s*(s+1)^k; reason: an integer implementation uses at least the stated sampling rate; the proof probability 1-k*(2k)^(-8) and 2/3 are preserved
--   - reading: G as above, with the preamble saying H-free while naming T-appearances → nonempty edge-disjoint role-preserving T-appearance collection covering every edge; reason: spells out the reduced-graph setup and resolves the named-pattern ambiguity; edgeless graphs cannot enter this discovery setup
--   - generalization: G is also epsilon-far with a maximal collection; success Omega(1) with q=O(1) queries → no farness or maximality hypothesis; one policy per n with explicit success at least 1-k/(2k)^8 and at least 2/3 and explicit query bound; reason: every graph in the source setup satisfies the Lean hypotheses; §7.3 uses only the covering, role and edge-disjointness properties and proves these constants, which depend on T alone and so specialize to Omega(1) and O(1)
--   - encoding: the edge query is undefined on an empty edge set in the displayed oracle description → a distinguished no-edge reply on edgeless inputs, and an isolation reply for empty neighbor sets; reason: completes the operational kernel on all input graphs, consistently with the source K2 discussion; nonempty-edge and neighbor laws are unchanged
-- source:
--   Oded Lachish, Amit Levi, Ilan Newman, Testability of General Graphs with Weak Query Oracles, STOC 2027 submission #274 (October 2026), p. 8 (PDF p. 9), Theorem 7 and preceding §4.1.2 setup; proof pp. 16–17 (PDF pp. 17–18)

import Mathlib
import Definitions.Def_WeakGraphOracles_OneSided_testing

set_option autoImplicit false

namespace WeakGraphOracles.OneSided

/-- Theorem 7, including the explicit success and query witnesses in §7.3.
The role map and packing are hypotheses of the analysis, never oracle inputs. -/
theorem role_preserving_tree_discovery (T : Pattern) (hT : T.graph.IsTree)
    (hk : 0 < (edges T.graph).card) :
    ∀ n, ∃ A : Policy n (treeQueryBound (edges T.graph).card), ValidPolicy true A ∧
      ∀ (G : SimpleGraph (Fin n)) (C : Finset (Appearance T G)),
        C.Nonempty → EdgeDisjoint C → RolePreserving C → copyUnion C = G →
        (1 - (edges T.graph).card /
            ((2 * (edges T.graph).card : ℝ) ^ 8) ≤ discoveryProbability T A G) ∧
        (2 : ℝ) / 3 ≤ discoveryProbability T A G := by sorry

end WeakGraphOracles.OneSided
