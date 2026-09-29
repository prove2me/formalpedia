-- Prove2me | Theorems.Thm_PreorderADI_Correlation_newsvendor_order_and_profit
-- name    : PreorderADI.Correlation.newsvendor_order_and_profit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:50:03.409043+00:00
-- url     : https://prove2.me/theorems/5164efba-54f9-4120-82bf-8d25937561d1
-- title:
--   §4 (1)–(2) — the second-period newsvendor orders Q(x) = μ̃_L(x) + z_L σ̃_L and earns Π_L(x)
-- statement:
--   Fix the model parameters under the standing assumptions, a correlation $\rho \in [0,1)$ and a realization $x$ of the standardized high-type demand $X$. In the second period the seller sells at $p_2 = v_L$ to the updated low-type demand $\tilde X_L(x) \sim N(\tilde\mu_L(x), \tilde\sigma_L^2)$, with $\tilde\mu_L(x) = \mu_L + \rho\sigma_L x$ and $\tilde\sigma_L = \sigma_L\sqrt{1-\rho^2}$. An order of $Q$ units earns the expected profit
--
--   $$
--   \pi(Q) = \mathbb E\big[v_L\min(Q, \tilde X_L(x)) - cQ\big].
--   $$
--
--   Let $z_L$ satisfy $\Phi(z_L) = (v_L - c)/v_L$. Then:
--
--   1. the order quantity $Q(x) = \tilde\mu_L(x) + z_L\tilde\sigma_L$ of (1) maximizes $\pi$ over all real $Q$;
--   2. it is the unique maximizer;
--   3. the maximal expected profit is (2):
--
--   $$
--   \pi(Q(x)) = \Pi_L(x) = (v_L - c)(\mu_L + \rho\sigma_L x) - v_L\phi(z_L)\sigma_L\sqrt{1-\rho^2}.
--   $$
--
--   This is the second-period building block of the preorder profit (4), whose second term is $\Pi_L(0)$.
--
--   **Formalization Note** The standing assumptions include the added $c > 0$, $\mu_H, \mu_L, \sigma_L > 0$ (see the model file). The optimization is over all real $Q$, since formula (1) itself can be negative for very negative $x$ under the normal model. $\rho < 1$ keeps the conditional law non-degenerate.
-- source:
--   Li and Zhang, Advance demand information, price discrimination, and preorder strategies, Manufacturing Service Oper. Management 15(1), 2013, p. 61, §4, (1)–(2)

import Mathlib
import Definitions.Def_PreorderADI_Correlation_Model

open MeasureTheory ProbabilityTheory

namespace PreorderADI.Correlation

theorem newsvendor_order_and_profit (P : Params) (hP : P.Standing)
    (ρ : ℝ) (hρ : ρ ∈ Set.Ico (0:ℝ) 1) (x : ℝ) :
    (∀ Q : ℝ, expectedSecondProfit P ρ x Q ≤ expectedSecondProfit P ρ x (orderQty P ρ x)) ∧
    (∀ Q : ℝ, (∀ Q' : ℝ, expectedSecondProfit P ρ x Q' ≤ expectedSecondProfit P ρ x Q) →
      Q = orderQty P ρ x) ∧
    expectedSecondProfit P ρ x (orderQty P ρ x) = secondProfit P ρ x := by sorry

end PreorderADI.Correlation
