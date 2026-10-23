-- Prove2me | Theorems.Thm_SalesRebate_NoIncreasing_theorem_2
-- name    : SalesRebate.NoIncreasing.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:03:16.736867+00:00
-- url     : https://prove2.me/theorems/36ce7942-b91b-40ea-bb63-c931252e4e79
-- title:
--   Theorem 2, p. 17 (PDF 17) — at an Assumption-1 price, no increasing sales-based reward program is profitable at any equilibrium cutoff
-- statement:
--   Let $(\theta, \sigma_\theta, \sigma_\epsilon)$ be a valid model and let the market price $p$ satisfy Assumption 1: $p$ maximizes the no-reward ex-ante profit $x\Phi((\theta - x)/\sigma)$ over prices $x \ge 0$. Let $r : [0,1] \to [0,p]$ be a weakly increasing reward program, a function of the sales volume, and let $c$ be any cutoff at which the threshold strategy $a_i = \mathbf 1\{v_i > c\}$ is an equilibrium (1) for the induced reward $\hat r(v) = r(\Phi((v-c)/\sigma_\epsilon))$. Then the program is not profitable:
--   $$\mathbb E_v\Big[(p - \hat r(v))\,\Phi\Big(\frac{v-c}{\sigma_\epsilon}\Big)\Big] \le \mathbb E_v\Big[p\,\Phi\Big(\frac{v-p}{\sigma_\epsilon}\Big)\Big].$$
--   The right-hand side is the expected profit of the no-reward case at the market price $p$.
--
--   This is the paper's message that inducing a positive network effect through a sales-based rebate cannot raise profit when the price is already optimal.
--
--   **Formalization Note** "Increasing" is weak monotonicity on $[0,1]$, so constant programs (price discounts) are included. The conclusion is required at every equilibrium cutoff $c$ of the consumers' subgame, with the same $c$ in $\hat r$, in (1) and in the profit. Assumption 1 is a standing assumption of §II; only its maximization clause, over prices $x \ge 0$, is used, not its first-order-condition characterization.
-- source:
--   Ajorlou, Jadbabaie, Sales-Based Rebate Design, arXiv:1902.09646v4, p. 17, Theorem 2 (proof p. 29); Assumption 1 p. 8

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Definitions.Def_SalesRebate_NoIncreasing_Setting

namespace SalesRebate.NoIncreasing

open MeasureTheory ProbabilityTheory BlackScholesModel

theorem theorem_2 (M : Model) (hM : M.Valid) (p : ℝ) (hp : M.IsMarketPrice p)
    (r : ℝ → ℝ) (hr : IsRewardProgram p r) (hmono : MonotoneOn r (Set.Icc 0 1))
    (c : ℝ) (hc : M.IsEquilibriumCutoff p (M.rhat r c) c) :
    ¬ M.IsProfitable p r c := by sorry

end SalesRebate.NoIncreasing
