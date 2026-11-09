-- Prove2me | Theorems.Thm_WeightedThreeSetPacking_Main_lemma_4_10
-- name    : WeightedThreeSetPacking.Main.lemma_4_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:51:47.533015+00:00
-- url     : https://prove2.me/theorems/6fa4d8b9-3823-42ac-85a7-c094e4ded7d5
-- title:
--   Lemma 4.10 — Actual gain and full 5.5 repair guarantee (Tong and Xu, arXiv:2610.10036v1, p. 24)
-- statement:
--   Under the standing setting of Tong and Xu, arXiv:2610.10036v1, Lemma 4.10, p. 24, use the inclusive neighborhoods, claws and exact parameters defined above.
--
--   Let the auxiliary family be selected by the fixed scaled Berman search with $\eta=1/11$. Let $\widehat\Delta$ be the sum of its declared gains and $\Delta_{\mathrm{rep}}=w(A^+)-w(A)$ the actual gain of simultaneous repair. Both conclusions hold: $$\Delta_{\mathrm{rep}}\ge\widehat\Delta,\qquad G(A,O)\le\frac{11}{2}\Delta_{\mathrm{rep}}.$$
--
--   This result provides the corresponding source statement in the dependency chain for the full approximation theorem.
--
--   Differences from the source:
--   - generalization: Positive rational set weights, an optimum packing O, and its rank-three conflict graph (or an analysis lift). → Positive real weights on A∪O, independent O, and finite graphs with the inherited two-sided inclusive degree bounds and maximum-neighbor assignment.; reason: These inequalities use positivity, independence and the rank-three degree bounds; every source instance and its weight-preserving lift satisfies these assumptions.
--   - encoding: Finite set families, inclusive neighborhoods, witnessed exchange multiarcs and finite sums. → Finite carrier types and Finsets, with one triple per witnessed arc and inclusive neighborhoods.; reason: This preserves common vertices, distinct-neighbor sums and incidence multiplicities.
--   - encoding: An auxiliary instance retaining a maximum-gain representative for each union, with fixed ties, and the scaled Berman routine. → Finite maximum selection with fixed code order, integer floor scaling at eta=1/11, and bounded squared search stopping when no improvement exists.; reason: The definitions compute representatives, the selected family and both gains without assuming any approximation guarantee.
--   - generalization: A is the Phase I output in the source standing setting. → Any A with the stated positivity, independent comparison packing, neighborhood degrees and maximum-neighbor assignment; no square local optimality assumption.; reason: These projection, graph-structure and repair statements do not use the local optimality or improving path of Phase I.
-- source:
--   Tong and Xu, arXiv:2610.10036v1, Lemma 4.10, p. 24; https://arxiv.org/abs/2610.10036v1

import Definitions.Def_WeightedThreeSetPacking_Main_Repairs

namespace WeightedThreeSetPacking.Main

open scoped BigOperators

/-- Tong and Xu, arXiv:2610.10036v1, Lemma 4.10, p. 24. -/
theorem lemma_4_10 {V : Type} [Fintype V] [DecidableEq V] (D : Analysis V)
    (hvalid : ValidAnalysis D)
    (sets : V → Finset ℕ) (hsets : Represents D sets) :
    declaredGain D sets ≤ actualGain D sets ∧
      residualTotal D ≤ (11/2 : ℝ) * actualGain D sets := by sorry

end WeightedThreeSetPacking.Main
