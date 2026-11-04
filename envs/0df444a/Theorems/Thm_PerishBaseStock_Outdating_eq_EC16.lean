-- Prove2me | Theorems.Thm_PerishBaseStock_Outdating_eq_EC16
-- name    : PerishBaseStock.Outdating.eq_EC16
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T02:43:37.475576+00:00
-- url     : https://prove2.me/theorems/48999048-04c0-4228-8807-6017775552fd
-- title:
--   (EC.16), p. ec6 — $\widetilde C_\theta(\widetilde S_\theta)\le\min_{0\le S\le m\underline D}\widetilde C_\theta(S)=\min_{0\le S\le m\underline D}N(S)$
-- statement:
--   Let $m\ge1$, $h,p>0$, $\theta\ge 0$, and let $\widetilde S_\theta$ minimize the heuristic cost $\widetilde C_\theta$ of (4) over $[0,\infty)$. Write $N(S)=h\mathbb E[(S-D)^+]+p\mathbb E[(D-S)^+]$ and $\underline D=\inf\{x:F(x)>0\}$. Then:
--
--   1. on $[0,m\underline D]$ the outdating term vanishes: $\widetilde C_\theta(S)=N(S)$ for every $0\le S\le m\underline D$;
--   2. $N$ attains its minimum over $[0,m\underline D]$;
--   3. $$\widetilde C_\theta(\widetilde S_\theta)=h\mathbb E[(\widetilde S_\theta-D)^+]+p\mathbb E[(D-\widetilde S_\theta)^+]+\frac{\theta}{m}\mathbb E\Big[\Big(\widetilde S_\theta-\sum_{i=1}^mD_i\Big)^+\Big]\le\min_{0\le S\le m\underline D}\big\{h\mathbb E[(S-D)^+]+p\mathbb E[(D-S)^+]\big\}.$$
--
--   Together, (1) and (2) say $\min_{0\le S\le m\underline D}\widetilde C_\theta(S)=\min_{0\le S\le m\underline D}N(S)$, the equality of (EC.16). The right side does not depend on $\theta$, which is what makes the outdating term of the heuristic level bounded uniformly in $\theta$.
--
--   **Formalization Note** The minimum is rendered as attainment (item 2) together with "$\le N(S)$ for every admissible $S$" (item 3), so no infimum convention is involved. $\theta$ ranges over $\mathbb R_{\ge0}$.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. ec6, App. B.3, (EC.16)

import Definitions.Def_PerishBaseStock_Outdating_Heuristic

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace PerishBaseStock.Outdating

theorem eq_EC16 (P : CappedBaseStock.DemandLaw) (c : Params) (θ : ℝ≥0) (St : ℝ≥0)
    (hSt : IsHeurMin P c θ St) :
    (∀ S : ℝ≥0, (S : ℝ) ≤ (c.m : ℝ) * lowerSupport P → heurCost P c θ S = nvCost P c S) ∧
      (∃ S₀ : ℝ≥0, (S₀ : ℝ) ≤ (c.m : ℝ) * lowerSupport P ∧
        ∀ S : ℝ≥0, (S : ℝ) ≤ (c.m : ℝ) * lowerSupport P → nvCost P c S₀ ≤ nvCost P c S) ∧
      (∀ S : ℝ≥0, (S : ℝ) ≤ (c.m : ℝ) * lowerSupport P → heurCost P c θ St ≤ nvCost P c S) := by sorry

end PerishBaseStock.Outdating
