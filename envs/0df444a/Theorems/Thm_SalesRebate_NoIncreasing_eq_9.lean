-- Prove2me | Theorems.Thm_SalesRebate_NoIncreasing_eq_9
-- name    : SalesRebate.NoIncreasing.eq_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:03:20.976009+00:00
-- url     : https://prove2.me/theorems/2cd5bdd0-81fe-44a7-933f-459d90a3a5c1
-- title:
--   (9), p. 16 (PDF 16) — under the indifference equation, profit = no-reward profit at price c + ∫_c^∞ (r_c − E[r̂|vᵢ])ψ
-- statement:
--   Let $(\theta, \sigma_\theta, \sigma_\epsilon)$ be a valid model, $p$ a price, $c$ a cutoff, and $\hat r : \mathbb R \to [0,p]$ a measurable reward. Write $r(x) = \mathbb E_{v\mid v_i = x}[\hat r(v)]$ for the reward a consumer with valuation $x$ expects and $r_c = r(c)$. If the indifference equation $c - p + r_c = 0$ holds, then
--   $$\mathbb E_v[\Pi(p, \hat r)] = \mathbb E_v[\Pi(c, 0)] + \int_c^\infty \big(r_c - r(x)\big)\,\psi(x)\,dx,$$
--   where $\mathbb E_v[\Pi(p,\hat r)]$ is the expected profit (2), $\mathbb E_v[\Pi(c, 0)]$ is the expected profit of offering the price $c$ with no reward and cutoff $c$, and $\psi$ is the ex-ante density of valuations.
--
--   The decomposition separates the profit into the profit of an equivalent plain price $c$ and the surplus the reward program extracts from buyers above the cutoff.
--
--   **Formalization Note** The outer equality of the three-line display (9) is posed. $\mathbb E_v[\Pi(c, 0)]$ is the profit (2) with reward $0$, price $c$ and cutoff $c$, not its closed form $c\Phi((\theta-c)/\sigma)$. Measurability and the range $[0,p]$ of $\hat r$ come from $\hat r \in L^\infty(\mathbb R; [0,p])$ (p. 10).
-- source:
--   Ajorlou, Jadbabaie, Sales-Based Rebate Design, arXiv:1902.09646v4, p. 16, (9)

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Definitions.Def_SalesRebate_NoIncreasing_Setting

namespace SalesRebate.NoIncreasing

open MeasureTheory ProbabilityTheory BlackScholesModel

theorem eq_9 (M : Model) (hM : M.Valid) (p : ℝ) (rhat : ℝ → ℝ)
    (hmeas : Measurable rhat) (hbound : ∀ v, rhat v ∈ Set.Icc 0 p) (c : ℝ)
    (hind : c - p + M.condReward rhat c = 0) :
    M.expectedProfit p rhat c = M.expectedProfit c (fun _ => 0) c +
      ∫ x in Set.Ioi c, (M.condReward rhat c - M.condReward rhat x) * M.psi x := by sorry

end SalesRebate.NoIncreasing
