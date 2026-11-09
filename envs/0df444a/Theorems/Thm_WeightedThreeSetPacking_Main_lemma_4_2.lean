-- Prove2me | Theorems.Thm_WeightedThreeSetPacking_Main_lemma_4_2
-- name    : WeightedThreeSetPacking.Main.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:50:30.846164+00:00
-- url     : https://prove2.me/theorems/048c76fb-772f-4acf-8a87-c99a4a1dda5e
-- title:
--   Lemma 4.2 — Internal edges stay in the first three layers (Tong and Xu, arXiv:2610.10036v1, p. 14)
-- statement:
--   Under the standing setting of Tong and Xu, arXiv:2610.10036v1, Lemma 4.2, p. 14, use the inclusive neighborhoods, claws and exact parameters defined above.
--
--   $$E(H[T])=E(H_{\le3}[T]),\qquad w_u>a^2w_v\quad((u,v)\in E(H[T])).$$
--
--   This result provides the corresponding source statement in the dependency chain for the full approximation theorem.
--
--   Differences from the source:
--   - generalization: Positive rational set weights, an optimum packing O, and its rank-three conflict graph (or an analysis lift). → Positive real weights on A∪O, independent O, and finite graphs with the inherited two-sided inclusive degree bounds and maximum-neighbor assignment.; reason: These inequalities use positivity, independence and the rank-three degree bounds; every source instance and its weight-preserving lift satisfies these assumptions.
--   - encoding: Finite set families, inclusive neighborhoods, witnessed exchange multiarcs and finite sums. → Finite carrier types and Finsets, with one triple per witnessed arc and inclusive neighborhoods.; reason: This preserves common vertices, distinct-neighbor sums and incidence multiplicities.
--   - generalization: A final piece after the Arkin–Hassin reduction with the larger fixed girth required for the full decomposition. → A computed final component with graph girth greater than twice its maximum possible vertex count.; reason: A cycle or parallel-arc obstruction in a final piece would give a conflict cycle of length at most twice that count; no full root/pendant hierarchy is needed for these final pieces.
--   - generalization: A is the Phase I output in the source standing setting. → Any A with the stated positivity, independent comparison packing, neighborhood degrees and maximum-neighbor assignment; no square local optimality assumption.; reason: These projection, graph-structure and repair statements do not use the local optimality or improving path of Phase I.
-- source:
--   Tong and Xu, arXiv:2610.10036v1, Lemma 4.2, p. 14; https://arxiv.org/abs/2610.10036v1

import Definitions.Def_WeightedThreeSetPacking_Main_Analysis

namespace WeightedThreeSetPacking.Main

open scoped BigOperators

/-- Tong and Xu, arXiv:2610.10036v1, Lemma 4.2, p. 14. -/
theorem lemma_4_2 {V : Type} [Fintype V] [DecidableEq V] (D : Analysis V)
    (hvalid : ValidAnalysis D)
    (hparameters : FixedParameters D) (hgirth : FinalHighGirth D)
    (T : Finset V) (hfinal : FinalComponent D T) :
    internalArcs D T 4 = internalArcs D T 3 ∧
    ∀ e ∈ internalArcs D T 4, a^2 * D.w e.2.2 < D.w e.2.1 := by sorry

end WeightedThreeSetPacking.Main
