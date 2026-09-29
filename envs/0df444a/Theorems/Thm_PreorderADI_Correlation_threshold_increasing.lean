-- Prove2me | Theorems.Thm_PreorderADI_Correlation_threshold_increasing
-- name    : PreorderADI.Correlation.threshold_increasing
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:53:27.459294+00:00
-- url     : https://prove2.me/theorems/5fd956ca-c1b0-4ae7-a81c-1f6366ee189f
-- title:
--   LEMMA 2(i) — for z_L ∈ (−λ_L/2, 0), the threshold μ̃(ρ) increases in ρ
-- statement:
--   Fix the model parameters under the standing assumptions, and suppose the critical-fractile quantile satisfies
--
--   $$
--   -\frac{\lambda_L}{2} < z_L < 0 .
--   $$
--
--   Then the threshold $\tilde\mu(\rho) = -v_L\phi(z_L)\sigma_L\big/\big(2\Delta z_L\phi(2z_L\sqrt{1-\rho^2} + \lambda_L)\big)$ of (6) is strictly increasing in $\rho$ on $[0,1)$.
--
--   Together with PROPOSITION 2(i) this says that, for moderately small margins, the preorder profit first decreases and then (possibly) increases in $\rho$.
--
--   **Formalization Note** "Increases" is read as strictly increasing (`StrictMonoOn` on $[0,1)$). The standing assumptions include the added $c > 0$, $\mu_H, \mu_L, \sigma_L > 0$.
-- source:
--   Li and Zhang, Advance demand information, price discrimination, and preorder strategies, Manufacturing Service Oper. Management 15(1), 2013, p. 62, §4.1, LEMMA 2(i)

import Mathlib
import Definitions.Def_PreorderADI_Correlation_Model

open MeasureTheory ProbabilityTheory

namespace PreorderADI.Correlation

theorem threshold_increasing (P : Params) (hP : P.Standing)
    (hz : -(P.lamL / 2) < P.zL) (hz0 : P.zL < 0) :
    StrictMonoOn (threshold P) (Set.Ico (0:ℝ) 1) := by sorry

end PreorderADI.Correlation
