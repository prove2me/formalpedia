-- Prove2me | Theorems.Thm_PerishBaseStock_LifoNegative_best_base_stock_limit
-- name    : PerishBaseStock.LifoNegative.best_base_stock_limit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T04:28:10.784679+00:00
-- url     : https://prove2.me/theorems/c1f96287-630c-43b0-8446-02f967c16ddf
-- title:
--   App. C.3, p. ec8 — $\lim_{\theta\to\infty} C_\theta(S^{LIFO,*}_\theta) = p(\mathbb E[D]-\underline D)$
-- statement:
--   Under the hypotheses of Proposition 1, fix the lifetime $m \ge 2$, costs $h, p > 0$, and a demand law with $S^{NP} > \underline D > 0$. For the LIFO system with outdating cost $\theta$, let $C^{LIFO}_\theta(S)$ be the long-run average cost of the base-stock policy $\pi_S$, and let $C_\theta(S^{LIFO,*}_\theta) = \inf_{S \ge 0} C^{LIFO}_\theta(S)$ be the best base-stock cost. Then
--   $$\lim_{\theta\to\infty} C_\theta(S^{LIFO,*}_\theta) = p(\mathbb E[D] - \underline D).$$
--
--   This is the first half of the proof of Proposition 1: as $\theta$ grows, the best base-stock policy can do no better than stocking up to the lower support $\underline D$.
--
--   **Formalization Note** $C_\theta(S^{LIFO,*}_\theta)$ is rendered as an infimum, since the paper does not show that a best base-stock level exists under LIFO. Costs are in $[0,\infty]$ and the limit is taken there, so a finite limit asserts in particular that the costs are eventually finite.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. ec8, App. C.3 (Proof of Proposition 1), first paragraph

import Definitions.Def_PerishBaseStock_LifoNegative_Model

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open CappedBaseStock LostSalesOrderUpTo.Asymptotic

namespace PerishBaseStock.LifoNegative

theorem best_base_stock_limit (P : DemandLaw) (c : Params) (hm : 2 ≤ c.m)
    (hNP : PerishBaseStock.Outdating.lowerSupport P < (newsvendorLevel P.law c.h c.p : ℝ))
    (hD : 0 < PerishBaseStock.Outdating.lowerSupport P) :
    Tendsto (fun θ : ℝ≥0 => bestBaseStockCost P (c.withTheta θ)) atTop
      (𝓝 (ENNReal.ofReal (c.p * (mean P - PerishBaseStock.Outdating.lowerSupport P)))) := by sorry

end PerishBaseStock.LifoNegative
