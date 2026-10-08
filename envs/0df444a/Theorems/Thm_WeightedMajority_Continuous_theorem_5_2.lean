-- Prove2me | Theorems.Thm_WeightedMajority_Continuous_theorem_5_2
-- name    : WeightedMajority.Continuous.theorem_5_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:19:32.62+00:00
-- url     : https://prove2.me/theorems/b7c14163-0497-4909-81be-c6c35a5cbf2b
-- title:
--   Theorem 5.2 — total absolute loss of WMC
-- statement:
--   Let WMC run on any finite sequence of trials with labels in $[0,1]$, using a finite nonempty pool whose predictions lie in $[0,1]$. Every initial weight is positive; at each trial, WMC predicts the pool's current weighted mean and updates each weight by any factor permitted by equation (5.1), with $0\le\beta<1$. If the final total weight is positive, its total absolute loss $m$ satisfies
--
--   $$m\le\frac{\ln(w_{\mathrm{init}}/w_{\mathrm{fin}})}{1-\beta}.$$
--
--   The result holds for every permitted factor choice and every finite instance and label sequence. It is the continuous-prediction counterpart of the paper's binary Weighted Majority bound.
--
--   **Formalization Note** The instances themselves are implicit in the supplied expert predictions, since the inequality uses them only through those predictions. The paper's bound is infinite when $w_{\mathrm{fin}}=0$; this real-valued statement covers its finite case.
-- source:
--   Littlestone and Warmuth, The Weighted Majority Algorithm, Information and Computation 108 (1994), p. 236, Theorem 5.2; https://doi.org/10.1006/inco.1994.1009

import Definitions.Def_WeightedMajority_Continuous_WMCRun

namespace WeightedMajority.Continuous

/-- Theorem 5.2, p. 236: the total absolute loss of any WMC run. -/
theorem theorem_5_2 {n t : ℕ} (beta : ℝ) (w : ℕ → Fin n → ℝ)
    (x : Fin t → Fin n → ℝ) (rho : Fin t → ℝ)
    (h : IsWMCRun beta w x rho) (hfin : 0 < WeightedMajority.Basic.totalWeight w t) :
    masterLoss w x rho ≤
      Real.log (WeightedMajority.Basic.totalWeight w 0 / WeightedMajority.Basic.totalWeight w t) / (1 - beta) := by sorry

end WeightedMajority.Continuous
