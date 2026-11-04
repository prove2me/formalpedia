-- Prove2me | Theorems.Thm_PerishBaseStock_LifoNegative_min_lower_bound_limit
-- name    : PerishBaseStock.LifoNegative.min_lower_bound_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T04:28:28.266986+00:00
-- url     : https://prove2.me/theorems/7d4a9a62-69f2-4421-b2c7-a8de7ff80a4b
-- title:
--   App. C.3, p. ec8 — $\lim_{\theta\to\infty}\min_{S\ge0}\hat C_{L,\theta}(S) = p(\mathbb E[D]-\underline D)$
-- statement:
--   Under the hypotheses of Proposition 1, fix the lifetime $m \ge 2$, costs $h, p > 0$, and a demand law with $S^{NP} > \underline D > 0$. Let $\hat C_{L,\theta}$ be the LIFO lower-bound function (11) with outdating cost $\theta$:
--   $$\hat C_{L,\theta}(S) = h\mathbb E[(S-D)^+] + p\mathbb E[(D-S)^+] + \frac{\theta}{m}\mathbb E[(S - \max\{D_1,\dots,D_m\})^+].$$
--   Then, with $\underline D$ the demand lower support,
--   $$\lim_{\theta\to\infty}\Big(\min_{S\ge 0}\hat C_{L,\theta}(S)\Big) = p(\mathbb E[D] - \underline D).$$
--
--   Together with Lemma 3 ($\hat C_L \le C^{LIFO}$), this is the lower half of the limit of the best base-stock cost.
--
--   **Formalization Note** The minimum is written as the infimum over $S \ge 0$ (the minimum exists, since $\hat C_{L,\theta}$ is continuous and tends to $\infty$; only its value enters). The function is real valued and nonnegative, so the infimum is a genuine one.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. ec8, App. C.3 (Proof of Proposition 1), first paragraph

import Definitions.Def_PerishBaseStock_LifoNegative_Model

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open CappedBaseStock LostSalesOrderUpTo.Asymptotic

namespace PerishBaseStock.LifoNegative

theorem min_lower_bound_limit (P : DemandLaw) (c : Params) (hm : 2 ≤ c.m)
    (hNP : PerishBaseStock.Outdating.lowerSupport P < (newsvendorLevel P.law c.h c.p : ℝ))
    (hD : 0 < PerishBaseStock.Outdating.lowerSupport P) :
    Tendsto (fun θ : ℝ≥0 => ⨅ S : ℝ≥0, lowerBoundCost P (c.withTheta θ) S) atTop
      (𝓝 (c.p * (mean P - PerishBaseStock.Outdating.lowerSupport P))) := by sorry

end PerishBaseStock.LifoNegative
