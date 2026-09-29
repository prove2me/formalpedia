-- Prove2me | Theorems.Thm_PreorderADI_Correlation_preorder_profit_deriv_sign
-- name    : PreorderADI.Correlation.preorder_profit_deriv_sign
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:52:58.949726+00:00
-- url     : https://prove2.me/theorems/18d12382-679e-48aa-a106-253aee3356cf
-- title:
--   PROPOSITION 2(i), via (5)–(6) — the sign of dΠ^p/dρ is the sign of μ̃(ρ) − μ_H
-- statement:
--   Fix the model parameters under the standing assumptions with $c < v_L < 2c$ (so $z_L < 0$), and a correlation $\rho \in (0,1)$. The preorder profit $\Pi^p(\rho) = (v_H - \Delta\xi(\rho) - c)\mu_H + \Pi_L(0)$ of (4) is differentiable at $\rho$, and its derivative $d = d\Pi^p/d\rho$ satisfies
--
--   $$
--   d > 0 \iff \mu_H < \tilde\mu(\rho), \qquad d < 0 \iff \mu_H > \tilde\mu(\rho),
--   $$
--
--   where $\tilde\mu(\rho)$ is the threshold (6).
--
--   This is the pointwise content of PROPOSITION 2(i): the decomposition (5) of $d\Pi^p/d\rho$ into the first-period effect $-\Delta\mu_H\,d\xi/d\rho$ and the second-period effect $d\Pi_L(0)/d\rho$ changes sign exactly where the high-type mean demand crosses the threshold.
--
--   **Formalization Note** At $\rho = 0$ the derivative is $0$ for every $\mu_H$, so the statement is on $(0,1)$. The standing assumptions include the added $c > 0$, $\mu_H, \mu_L, \sigma_L > 0$.
-- source:
--   Li and Zhang, Advance demand information, price discrimination, and preorder strategies, Manufacturing Service Oper. Management 15(1), 2013, p. 62, §4.1, (5), (6) and PROPOSITION 2(i)

import Mathlib
import Definitions.Def_PreorderADI_Correlation_Model

open MeasureTheory ProbabilityTheory

namespace PreorderADI.Correlation

theorem preorder_profit_deriv_sign (P : Params) (hP : P.Standing)
    (h2c : P.vL < 2 * P.c) (ρ : ℝ) (hρ : ρ ∈ Set.Ioo (0:ℝ) 1) :
    ∃ d : ℝ, HasDerivAt (preorderProfit P) d ρ ∧
      (0 < d ↔ P.muH < threshold P ρ) ∧ (d < 0 ↔ threshold P ρ < P.muH) := by sorry

end PreorderADI.Correlation
