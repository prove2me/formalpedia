-- Prove2me | Theorems.Thm_PreorderADI_Correlation_preorder_profit_monotone_in_rho
-- name    : PreorderADI.Correlation.preorder_profit_monotone_in_rho
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:54:29.21328+00:00
-- url     : https://prove2.me/theorems/10857697-c333-48ed-a688-7a7be6c6f6cb
-- title:
--   PROPOSITION 2 — Π^p increases in ρ exactly where μ_H < μ̃(ρ) when v_L < 2c, and always when v_L ≥ 2c
-- statement:
--   Consider the preorder model under its standing assumptions, and the seller's preorder profit (4)
--
--   $$
--   \Pi^p(\rho) = (v_H - \Delta\xi(\rho) - c)\mu_H + \Pi_L(0)
--   $$
--
--   as a function of the demand correlation $\rho \in [0,1)$, with the threshold $\tilde\mu(\rho)$ of (6).
--
--   1. If $c < v_L < 2c$ (equivalently $z_L < 0$), then on every interval $I \subseteq [0,1)$:
--      - if $\mu_H < \tilde\mu(\rho)$ for all $\rho \in I$, then $\Pi^p$ is strictly increasing on $I$;
--      - if $\mu_H \ge \tilde\mu(\rho)$ for all $\rho \in I$, then $\Pi^p$ is strictly decreasing on $I$.
--   2. If $v_L \ge 2c$ (equivalently $z_L \ge 0$), then $\Pi^p$ is strictly increasing on all of $[0,1)$.
--
--   More accurate advance demand information therefore benefits the seller when the low-type valuation is large, or when the high-type demand is small relative to the threshold; otherwise the loss in preorder price outweighs the gain in second-period profit.
--
--   **Formalization Note** "$\Pi^p$ increases in $\rho$ when $\mu_H < \tilde\mu(\rho)$" is a pointwise condition on $\rho$; it is formalized as monotonicity on every order-connected set $I \subseteq [0,1)$ on which the condition holds. Monotonicity is strict in both directions. The paper's further sentence of (i), "there exists an $\varepsilon_v > 0$ such that $\Pi^p$ always decreases in $\rho$ if $v_L < c + \varepsilon_v$", is false in the paper's own model and is not formalized: as $v_L \downarrow c$, $z_L \to -\infty$ and $\tilde\mu(\rho) \to \infty$ for $\rho$ below roughly $\sqrt 3/2$, so $\Pi^p$ increases there for every fixed $\mu_H$ (for instance $\mu_L = 5$, $\lambda_L = 4.5$, $v_H = 2$, $c = 1$, $\delta = 1$, $v_L = 1 + 10^{-20}$ gives $\Pi^p(0.3) > \Pi^p(0.1)$ for $\mu_H \in \{0.001, 1, 100\}$). $\Pi^p$ is taken from (4) as a definition; PROPOSITION 1, which derives it as the unique equilibrium profit, is not formalized. The standing assumptions include the added $c > 0$, $\mu_L, \sigma_L > 0$ and $\mu_H > 0$; the last is needed in (ii).
-- source:
--   Li and Zhang, Advance demand information, price discrimination, and preorder strategies, Manufacturing Service Oper. Management 15(1), 2013, p. 62, §4.1, PROPOSITION 2 (without the ε_v sentence of (i))

import Mathlib
import Definitions.Def_PreorderADI_Correlation_Model

open MeasureTheory ProbabilityTheory

namespace PreorderADI.Correlation

theorem preorder_profit_monotone_in_rho (P : Params) (hP : P.Standing) :
    (P.vL < 2 * P.c →
      ∀ I ⊆ Set.Ico (0:ℝ) 1, I.OrdConnected →
        ((∀ ρ ∈ I, P.muH < threshold P ρ) → StrictMonoOn (preorderProfit P) I) ∧
        ((∀ ρ ∈ I, threshold P ρ ≤ P.muH) → StrictAntiOn (preorderProfit P) I)) ∧
    (2 * P.c ≤ P.vL → StrictMonoOn (preorderProfit P) (Set.Ico (0:ℝ) 1)) := by sorry

end PreorderADI.Correlation
