-- Prove2me | Theorems.Thm_WeightedMajority_Continuous_lemma_5_3
-- name    : WeightedMajority.Continuous.lemma_5_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:19:27.974035+00:00
-- url     : https://prove2.me/theorems/4881ab04-cee5-4089-9a8a-ea1cd719da31
-- title:
--   Lemma 5.3 — absolute loss under the upper update bound
-- statement:
--   Under Lemma 5.2's assumptions, with positive final total weight, the weighted mean predictions $\gamma^{(j)}$ have total absolute loss bounded by
--
--   $$\sum_j|\gamma^{(j)}-\rho^{(j)}|\le\frac{\ln(w_{\mathrm{init}}/w_{\mathrm{fin}})}{1-\beta}.$$
--
--   This inequality applies to any nonnegative weight sequence satisfying the upper update bound, independently of how its update factors were selected.
--
--   **Formalization Note** Positive final weight selects the finite-valued case of the paper's bound; when final weight vanishes, its right side is interpreted as infinite.
-- source:
--   Littlestone and Warmuth, The Weighted Majority Algorithm, Information and Computation 108 (1994), p. 236, Lemma 5.3; https://doi.org/10.1006/inco.1994.1009

import Definitions.Def_WeightedMajority_Continuous_WMCRun

namespace WeightedMajority.Continuous

/-- Lemma 5.3, p. 236: the absolute loss bound under Lemma 5.2's conditions. -/
theorem lemma_5_3 {n t : ℕ} (beta : ℝ) (w : ℕ → Fin n → ℝ)
    (x : Fin t → Fin n → ℝ) (rho : Fin t → ℝ)
    (h : PotentialConditions beta w x rho) (hfin : 0 < WeightedMajority.Basic.totalWeight w t) :
    masterLoss w x rho ≤
      Real.log (WeightedMajority.Basic.totalWeight w 0 / WeightedMajority.Basic.totalWeight w t) / (1 - beta) := by sorry

end WeightedMajority.Continuous
