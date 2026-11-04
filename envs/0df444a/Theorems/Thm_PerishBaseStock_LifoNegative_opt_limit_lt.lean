-- Prove2me | Theorems.Thm_PerishBaseStock_LifoNegative_opt_limit_lt
-- name    : PerishBaseStock.LifoNegative.opt_limit_lt
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T04:28:17.307702+00:00
-- url     : https://prove2.me/theorems/f1eb44fc-7703-4a89-bde3-204976429bc5
-- title:
--   App. C.3, p. ec9 — $\lim_{\theta\to\infty}\mathrm{OPT}^{LIFO}_\theta < p(\mathbb E[D]-\underline D)$
-- statement:
--   Consider the LIFO system with lifetime $m \ge 2$, costs $h, p > 0$, and a demand law with $S^{NP} > \underline D > 0$. Let $\mathrm{OPT}^{LIFO}_\theta$ be the optimal long-run average cost over all admissible policies when the outdating cost is $\theta$. Then the limit as $\theta\to\infty$ exists and
--   $$\lim_{\theta\to\infty}\mathrm{OPT}^{LIFO}_\theta < p(\mathbb E[D] - \underline D).$$
--
--   With the limit of the best base-stock cost, this gives Proposition 1.
--
--   **Formalization Note** The limit is taken in $[0,\infty]$; the statement asserts that it exists and is strictly below $p(\mathbb E[D]-\underline D)$.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. ec9, App. C.3 (Proof of Proposition 1), last paragraph

import Definitions.Def_PerishBaseStock_LifoNegative_Model

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open CappedBaseStock LostSalesOrderUpTo.Asymptotic

namespace PerishBaseStock.LifoNegative

theorem opt_limit_lt (P : DemandLaw) (c : Params) (hm : 2 ≤ c.m)
    (hNP : PerishBaseStock.Outdating.lowerSupport P < (newsvendorLevel P.law c.h c.p : ℝ))
    (hD : 0 < PerishBaseStock.Outdating.lowerSupport P) :
    ∃ L : ℝ≥0∞, Tendsto (fun θ : ℝ≥0 => OPT P (c.withTheta θ)) atTop (𝓝 L) ∧
      L < ENNReal.ofReal (c.p * (mean P - PerishBaseStock.Outdating.lowerSupport P)) := by sorry

end PerishBaseStock.LifoNegative
