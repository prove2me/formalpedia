-- Prove2me | Theorems.Thm_WeightedThreeSetPacking_Main_lemma_4_7
-- name    : WeightedThreeSetPacking.Main.lemma_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:50:33.408345+00:00
-- url     : https://prove2.me/theorems/9beeb072-a99f-471e-944f-d6b67cc2941d
-- title:
--   Lemma 4.7 — Exact capped square-mass to mass minimum (Tong and Xu, arXiv:2610.10036v1, p. 19)
-- statement:
--   Under the standing setting of Tong and Xu, arXiv:2610.10036v1, Lemma 4.7, p. 19, use the inclusive neighborhoods, claws and exact parameters defined above.
--
--   For real $0\le S\le2mq^2$, write $S=hq^2+\theta$ with $h\in\mathbb N$ and $0\le\theta<q^2$. For the genuine minimum over at most $2m$ real coordinates bounded between zero and $q$ with squared sum at least $S$, $$\beta_{\min}(S)=hq+\sqrt\theta.$$ A feasible vector attains this value. The formula includes both endpoints.
--
--   This result provides the corresponding source statement in the dependency chain for the full approximation theorem.
--
--   Differences from the source:
--   - generalization: The singleton application uses 1≤m≤3. → Any natural m, including zero, with the same feasibility domain.; reason: The cap-filling minimum formula holds in every finite dimension; m=0 forces S=h=theta=0.
--   - encoding: A minimum over at most 2m real coordinates. → An infimum over exactly 2m zero-padded real coordinates, together with explicit attainment.; reason: Padding changes neither feasibility nor the objective, and attainment preserves the source minimum.
-- source:
--   Tong and Xu, arXiv:2610.10036v1, Lemma 4.7, p. 19; https://arxiv.org/abs/2610.10036v1

import Definitions.Def_WeightedThreeSetPacking_Main_Analysis

namespace WeightedThreeSetPacking.Main

open scoped BigOperators

/-- Tong and Xu, arXiv:2610.10036v1, Lemma 4.7, p. 19. -/
theorem lemma_4_7 (m : ℕ) (S : ℝ) (hS : 0 ≤ S ∧ S ≤ 2*(m : ℝ)*q^2)
    (h : ℕ) (theta : ℝ) (hdecomp : S = (h : ℝ)*q^2 + theta)
    (htheta : 0 ≤ theta ∧ theta < q^2) :
    betaMinimum m S = (h : ℝ)*q + Real.sqrt theta ∧
    ∃ z : Fin (2*m) → ℝ, cappedFeasible m S z ∧
      (∑ i, z i) = betaMinimum m S := by sorry

end WeightedThreeSetPacking.Main
