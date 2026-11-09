-- Prove2me | Theorems.Thm_WeightedThreeSetPacking_Main_lemma_3_1
-- name    : WeightedThreeSetPacking.Main.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:50:11.877203+00:00
-- url     : https://prove2.me/theorems/1a96d38b-ad93-4924-bf11-9cdab756d681
-- title:
--   Lemma 3.1 — Master charging inequality (Tong and Xu, arXiv:2610.10036v1, p. 7)
-- statement:
--   Under the standing setting of Tong and Xu, arXiv:2610.10036v1, Lemma 3.1, p. 7, use the inclusive neighborhoods, claws and exact parameters defined above.
--
--   $$2w(O)\le w(A)+\sum_{o\in O}w(N(o,A))-\sum_{v\in A}(\Delta_v/w_v+\Psi_v/w_v).$$
--
--   This result provides the corresponding source statement in the dependency chain for the full approximation theorem.
--
--   Differences from the source:
--   - generalization: Positive rational set weights, an optimum packing O, and its rank-three conflict graph (or an analysis lift). → Positive real weights on A∪O, independent O, and finite graphs with the inherited two-sided inclusive degree bounds and maximum-neighbor assignment.; reason: These inequalities use positivity, independence and the rank-three degree bounds; every source instance and its weight-preserving lift satisfies these assumptions.
--   - encoding: Finite set families, inclusive neighborhoods, witnessed exchange multiarcs and finite sums. → Finite carrier types and Finsets, with one triple per witnessed arc and inclusive neighborhoods.; reason: This preserves common vertices, distinct-neighbor sums and incidence multiplicities.
-- source:
--   Tong and Xu, arXiv:2610.10036v1, Lemma 3.1, p. 7; https://arxiv.org/abs/2610.10036v1

import Definitions.Def_WeightedThreeSetPacking_Main_Analysis

namespace WeightedThreeSetPacking.Main

open scoped BigOperators

/-- Tong and Xu, arXiv:2610.10036v1, Lemma 3.1, p. 7. -/
theorem lemma_3_1 {V : Type} [Fintype V] [DecidableEq V] (D : Analysis V)
    (hvalid : ValidAnalysis D)
    (hlocal : SquareLocal D 1) :
    2 * mass D D.O ≤ mass D D.A +
      (∑ o ∈ D.O, mass D (neighbors D {o} D.A)) - slackSum D D.A := by sorry

end WeightedThreeSetPacking.Main
