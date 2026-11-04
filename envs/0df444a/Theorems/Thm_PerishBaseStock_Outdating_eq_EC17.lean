-- Prove2me | Theorems.Thm_PerishBaseStock_Outdating_eq_EC17
-- name    : PerishBaseStock.Outdating.eq_EC17
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T02:43:41.938619+00:00
-- url     : https://prove2.me/theorems/235784de-e15a-462e-b244-0615eae17cb3
-- title:
--   (EC.17), p. ec7 — the limit $\widetilde S_\infty$ of the least heuristic levels and $N(\widetilde S_\infty)\ge\min_{0\le S\le m\underline D}N(S)$
-- statement:
--   Let $m\ge1$, $h,p>0$, and for $\theta\ge0$ let $\widetilde S_\theta$ be the **least** minimizer of the heuristic cost $\widetilde C_\theta$ of (4) over $[0,\infty)$. Write $N(S)=h\mathbb E[(S-D)^+]+p\mathbb E[(D-S)^+]$. Then the limit $\widetilde S_\infty=\lim_{\theta\to\infty}\widetilde S_\theta$ exists, and
--   $$\lim_{\theta\to\infty}\big\{h\mathbb E[(\widetilde S_\theta-D)^+]+p\mathbb E[(D-\widetilde S_\theta)^+]\big\}=h\mathbb E[(\widetilde S_\infty-D)^+]+p\mathbb E[(D-\widetilde S_\infty)^+]\ge\min_{0\le S\le m\underline D}\big\{h\mathbb E[(S-D)^+]+p\mathbb E[(D-S)^+]\big\}.$$
--
--   Combined with (EC.16), this squeezes the outdating term $\theta\mathbb E[(\widetilde S_\theta-\sum_{i=1}^mD_i)^+]$ of the heuristic level to zero.
--
--   **Formalization Note** The paper defines $\widetilde S_\infty$ as $\lim_\theta\widetilde S_\theta$, which it justifies by "$\widetilde S_\theta$ decreases in $\theta$". That monotonicity holds for the least minimizer but not for an arbitrary selection of minimizers, so the statement is posed for the least minimizer; the existence of the limit is part of the conclusion. The minimum on the right is the real infimum of $N$ over $\{0\le S\le m\underline D\}$, which is attained (see (EC.16)). $\theta$ ranges over $\mathbb R_{\ge0}$.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), pp. ec6–ec7, App. B.3, (EC.17)

import Definitions.Def_PerishBaseStock_Outdating_Heuristic

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace PerishBaseStock.Outdating

theorem eq_EC17 (P : CappedBaseStock.DemandLaw) (c : Params) :
    ∃ Sinf : ℝ≥0,
      Tendsto (fun θ : ℝ≥0 => leastHeurMin P c θ) atTop (𝓝 Sinf) ∧
      Tendsto (fun θ : ℝ≥0 => nvCost P c (leastHeurMin P c θ)) atTop (𝓝 (nvCost P c Sinf)) ∧
      nvMinBelow P c ≤ nvCost P c Sinf := by sorry

end PerishBaseStock.Outdating
