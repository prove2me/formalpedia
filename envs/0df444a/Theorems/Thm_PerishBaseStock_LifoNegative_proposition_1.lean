-- Prove2me | Theorems.Thm_PerishBaseStock_LifoNegative_proposition_1
-- name    : PerishBaseStock.LifoNegative.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T04:28:28.203275+00:00
-- url     : https://prove2.me/theorems/b409e286-f951-4d71-89a3-98aeb6abd512
-- title:
--   Proposition 1 — under LIFO with $m\ge2$ and $S^{NP}>\underline D>0$, $\lim_{\theta\to\infty}(C_\theta(S^{LIFO,*}_\theta)-\mathrm{OPT}_\theta)>0$
-- statement:
--   Consider the perishable inventory system with lost sales, zero lead time and LIFO issuance, with lifetime $m$, unit holding cost $h > 0$, unit penalty $p > 0$ and unit outdating cost $\theta \ge 0$, and i.i.d. demand $D$ with lower support $\underline D$ and newsvendor level $S^{NP} = F^{-1}(p/(p+h))$. Let $C^{LIFO}_\theta(S^{LIFO,*}_\theta)$ be the best base-stock cost and $\mathrm{OPT}^{LIFO}_\theta$ the optimal cost over all admissible policies.
--
--   **Proposition 1.** If $m \ge 2$ and $S^{NP} > \underline D > 0$, then
--   $$\lim_{\theta\to\infty}\big(C^{LIFO}_\theta(S^{LIFO,*}_\theta) - \mathrm{OPT}^{LIFO}_\theta\big) > 0.$$
--
--   So under LIFO the best base-stock policy is not asymptotically optimal as the outdating cost grows, unless $m = 1$, $S^{NP} \le \underline D$ or $\underline D = 0$ (the last is Theorem 5(c)).
--
--   **Formalization Note** $C^{LIFO}_\theta(S^{LIFO,*}_\theta)$ is rendered as $\inf_{S\ge0} C^{LIFO}_\theta(S)$, since the existence of a best base-stock level under LIFO is not shown. The statement asserts that both costs are finite for every $\theta \ge 0$, and that the difference of their real values converges to a strictly positive limit as $\theta\to\infty$ along $[0,\infty)$; "$\lim > 0$" is read as "the limit exists and is positive".
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. 17, Proposition 1

import Definitions.Def_PerishBaseStock_LifoNegative_Model

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open CappedBaseStock LostSalesOrderUpTo.Asymptotic

namespace PerishBaseStock.LifoNegative

theorem proposition_1 (P : DemandLaw) (c : Params) (hm : 2 ≤ c.m)
    (hNP : PerishBaseStock.Outdating.lowerSupport P < (newsvendorLevel P.law c.h c.p : ℝ))
    (hD : 0 < PerishBaseStock.Outdating.lowerSupport P) :
    (∀ θ : ℝ≥0, bestBaseStockCost P (c.withTheta θ) ≠ ⊤ ∧ OPT P (c.withTheta θ) ≠ ⊤) ∧
    ∃ gap : ℝ, 0 < gap ∧
      Tendsto (fun θ : ℝ≥0 =>
        (bestBaseStockCost P (c.withTheta θ)).toReal - (OPT P (c.withTheta θ)).toReal)
        atTop (𝓝 gap) := by sorry

end PerishBaseStock.LifoNegative
