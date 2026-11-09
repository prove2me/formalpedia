-- Prove2me | Theorems.Thm_WeakGraphOracles_OneSided_singleton_acyclic_testability
-- name    : WeakGraphOracles.OneSided.singleton_acyclic_testability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:22:59.599811+00:00
-- url     : https://prove2.me/theorems/c8dbd14c-62da-4cd9-b719-9ca72a515ea2
-- title:
--   Theorem 6 — full singleton acyclicity characterization
-- statement:
--   Let $H$ be a fixed connected finite simple graph with at least one edge. In GEN1, with edge-deletion distance and one-sided correctness at threshold $2/3$,
--
--   $$\operatorname{Test}_{\mathrm{GEN1}}(\{H\})\iff H\text{ is acyclic}.$$
--
--   Testability quantifies over every positive proximity and a size-independent finite query bound. It allows arbitrary adaptive randomized policies on all finite input graphs, including disconnected inputs and isolated vertices. Both implications are asserted. This completed singleton result is used in the family theorem's tree case.
--
--   Differences from the source:
--   - encoding: finite simple graphs with labels [n] → SimpleGraph (Fin n), with finite patterns carrying their own order; reason: relabeling by the standard bijection preserves every graph, appearance, degree and edge count
--   - encoding: adaptive randomized algorithms with at most q oracle queries → PMF over complete deterministic query plans of depth at most q, executed against fresh uniform response kernels; reason: finite query and reply alphabets at each fixed n and q make this equivalent to arbitrary internal randomization; no hidden graph is supplied to a policy
--   - encoding: minimum number of actual edge deletions, with strict farness → ENNReal infimum of cardinalities of feasible deletion sets; comparison with ENNReal.ofReal of epsilon times the edge or vertex count; reason: the feasible family is finite and nonempty for the stated patterns, so the infimum is its attained integer minimum; empty feasible families have value infinity, never a fabricated zero
--   - encoding: the edge query is undefined on an empty edge set in the displayed oracle description → a distinguished no-edge reply on edgeless inputs, and an isolation reply for empty neighbor sets; reason: completes the operational kernel on all input graphs, consistently with the source K2 discussion; nonempty-edge and neighbor laws are unchanged
-- source:
--   Oded Lachish, Amit Levi, Ilan Newman, Testability of General Graphs with Weak Query Oracles, STOC 2027 submission #274 (October 2026), p. 6 (PDF p. 7), Theorem 6 and §4.1 standing assumptions

import Mathlib
import Definitions.Def_WeakGraphOracles_OneSided_testing

set_option autoImplicit false

namespace WeakGraphOracles.OneSided

/-- Theorem 6 in full, under the standing connected non-isolated setting. -/
theorem singleton_acyclic_testability (H : Pattern) (hH : EligiblePattern H) :
    GEN1Testable {H} ↔ H.graph.IsAcyclic := by sorry

end WeakGraphOracles.OneSided
