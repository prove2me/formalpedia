-- Prove2me | Theorems.Thm_PreorderADI_Correlation_second_profit_deriv
-- name    : PreorderADI.Correlation.second_profit_deriv
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:52:21.621531+00:00
-- url     : https://prove2.me/theorems/7eaae05f-24d2-454b-a1e5-56805755fea4
-- title:
--   §4.1, after (5) — (d/dρ)Π_L(0) = v_Lφ(z_L)σ_L ρ/√(1 − ρ²) > 0
-- statement:
--   Fix the model parameters under the standing assumptions and a correlation $\rho \in (0,1)$. The expected second-period profit $\Pi_L(0) = (v_L - c)\mu_L - v_L\phi(z_L)\sigma_L\sqrt{1-\rho^2}$ of (2), viewed as a function of $\rho$, is differentiable at $\rho$ with
--
--   $$
--   \frac{d}{d\rho}\Pi_L(0) = v_L\phi(z_L)\sigma_L\frac{\rho}{\sqrt{1-\rho^2}},
--   $$
--
--   and this derivative is positive.
--
--   More accurate advance demand information improves the seller's second-period matching of supply with demand; this is the positive term in the decomposition (5) of $d\Pi^p/d\rho$.
--
--   **Formalization Note** The derivative is $0$ at $\rho = 0$, so positivity is stated on $(0,1)$. The standing assumptions include the added $c > 0$, $\mu_H, \mu_L, \sigma_L > 0$.
-- source:
--   Li and Zhang, Advance demand information, price discrimination, and preorder strategies, Manufacturing Service Oper. Management 15(1), 2013, p. 62, §4.1, text after (5)

import Mathlib
import Definitions.Def_PreorderADI_Correlation_Model

open MeasureTheory ProbabilityTheory

namespace PreorderADI.Correlation

theorem second_profit_deriv (P : Params) (hP : P.Standing)
    (ρ : ℝ) (hρ : ρ ∈ Set.Ioo (0:ℝ) 1) :
    HasDerivAt (fun r => secondProfit P r 0)
      (P.vL * stdNormalPdf P.zL * P.sigmaL * (ρ / Real.sqrt (1 - ρ ^ 2))) ρ ∧
    0 < P.vL * stdNormalPdf P.zL * P.sigmaL * (ρ / Real.sqrt (1 - ρ ^ 2)) := by sorry

end PreorderADI.Correlation
