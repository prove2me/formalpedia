-- Prove2me | Theorems.Thm_WeightedThreeSetPacking_Main_lemma_4_4
-- name    : WeightedThreeSetPacking.Main.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:51:44.824714+00:00
-- url     : https://prove2.me/theorems/25d5cf2c-e684-4f0e-9187-7b3b34b2727a
-- title:
--   Lemma 4.4 — Nonsingleton final-component bound (Tong and Xu, arXiv:2610.10036v1, p. 15)
-- statement:
--   Under the standing setting of Tong and Xu, arXiv:2610.10036v1, Lemma 4.4, p. 15, use the inclusive neighborhoods, claws and exact parameters defined above. Here T is a nonsingleton final component.
--
--   $$\sum_{v\in T}(\Delta_v/w_v+\Psi_v/w_v)\ge Q(T)+(c-3\delta)w(T).$$
--
--   This result provides the corresponding source statement in the dependency chain for the full approximation theorem.
--
--   Differences from the source:
--   - generalization: Positive rational set weights, an optimum packing O, and its rank-three conflict graph (or an analysis lift). → Positive real weights on A∪O, independent O, and finite graphs with the inherited two-sided inclusive degree bounds and maximum-neighbor assignment.; reason: These inequalities use positivity, independence and the rank-three degree bounds; every source instance and its weight-preserving lift satisfies these assumptions.
--   - encoding: Finite set families, inclusive neighborhoods, witnessed exchange multiarcs and finite sums. → Finite carrier types and Finsets, with one triple per witnessed arc and inclusive neighborhoods.; reason: This preserves common vertices, distinct-neighbor sums and incidence multiplicities.
--   - generalization: A final piece after the Arkin–Hassin reduction with the larger fixed girth required for the full decomposition. → A computed final component with graph girth greater than twice its maximum possible vertex count.; reason: A cycle or parallel-arc obstruction in a final piece would give a conflict cycle of length at most twice that count; no full root/pendant hierarchy is needed for these final pieces.
--   - generalization: The Phase I packing in the source standing setting. → Every packing satisfying the same fixed s₀-exchange square local optimality.; reason: Only the resulting local optimality, rather than the execution path of Phase I, is used.
-- source:
--   Tong and Xu, arXiv:2610.10036v1, Lemma 4.4, p. 15; https://arxiv.org/abs/2610.10036v1

import Definitions.Def_WeightedThreeSetPacking_Main_Analysis

namespace WeightedThreeSetPacking.Main

open scoped BigOperators

/-- Tong and Xu, arXiv:2610.10036v1, Lemma 4.4, p. 15. -/
theorem lemma_4_4 {V : Type} [Fintype V] [DecidableEq V] (D : Analysis V)
    (hvalid : ValidAnalysis D)
    (hparameters : FixedParameters D) (hgirth : FinalHighGirth D)
    (T : Finset V) (hfinal : FinalComponent D T)
    (hlocal : SquareLocal D s₀)
    (hnonsingleton : 2 ≤ T.card) :
    slackSum D T ≥ layerCredit D T + (c - 3 * delta) * mass D T := by sorry

end WeightedThreeSetPacking.Main
