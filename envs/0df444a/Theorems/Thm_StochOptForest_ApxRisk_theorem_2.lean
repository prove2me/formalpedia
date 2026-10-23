-- Prove2me | Theorems.Thm_StochOptForest_ApxRisk_theorem_2
-- name    : StochOptForest.ApxRisk.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:29:12.417006+00:00
-- url     : https://prove2.me/theorems/e281def6-e3dd-4f53-b7ee-657e00d3fa47
-- title:
--   Theorem 2, pp. 9–10 — |C^oracle − p₀f₀(z₀) − C^apx-risk| = o(p₀D₀²) as the region R₀ shrinks to a point with a nondegenerate optimum
-- statement:
--   Let $\mu$ be the law of the features on $\mathbb R^p$ (a probability measure) and $\bar c(x,z)=\mathbb E[c(z;Y)\mid X=x]$ the regression cost. Assume:
--
--   1. for every $x$, $z\mapsto\bar c(x,z)$ is twice continuously differentiable;
--   2. $\bar c$, $\nabla_z\bar c$ and $\nabla^2_z\bar c$ are $L$-Lipschitz in $x$, uniformly in $z$ (condition 4, as used in the proof);
--   3. at an anchor point $\bar x\in\mathbb R^p$, $\bar c(\bar x,\cdot)$ has a unique minimizer $\bar z$, its Hessian there is positive definite, and some sublevel set $\{z:\bar c(\bar x,z)\le\alpha\}$ with $\alpha>\bar c(\bar x,\bar z)$ is bounded.
--
--   For a region $R_0=R_1\cup R_2$ split into disjoint measurable $R_1,R_2$ of positive probability, let $p_j$, $f_j$ ($j=0,1,2$) be the probabilities and region averages, $\mathcal D_0=\sup_{x,x'\in R_0}\|x-x'\|_2$ its diameter, $\mathcal C^{\mathrm{oracle}}$ the oracle criterion (8) and $\mathcal C^{\mathrm{apx\text{-}risk}}$ the approximate risk criterion (13). Suppose that for both $j=1,2$ the conditions of Theorem 2 hold:
--
--   1. $f_0$ and $f_j$ are twice continuously differentiable;
--   2. there are $\alpha$ and a bounded set containing every sublevel set $\{z:f_0(z)+t(f_j(z)-f_0(z))\le\alpha\}$, $t\in[0,1]$, each of which is nonempty;
--   3. for every $t\in[0,1]$, $f_0+t(f_j-f_0)$ has a unique minimizer, at which its Hessian is positive definite.
--
--   Then for every $\varepsilon>0$ there is $\delta>0$ such that every such split with $R_0$ inside the ball of radius $\delta$ around $\bar x$, with $z_0$ the unique minimizer of $f_0$, satisfies
--   $$\bigl|\mathcal C^{\mathrm{oracle}}(R_1,R_2)-p_0f_0(z_0)-\mathcal C^{\mathrm{apx\text{-}risk}}(R_1,R_2)\bigr|\le\varepsilon\,p_0\,\mathcal D_0^2 .$$
--   In short, the error is $o(p_0\mathcal D_0^2)$ as $R_0$ shrinks to $\bar x$.
--
--   This is the paper's justification for growing the trees of a stochastic optimization forest with the approximate risk criterion: it ranks candidate splits like the oracle criterion, up to an error negligible compared with the criterion's own size $O(p_0\mathcal D_0^2)$, while needing only one Hessian per parent region.
--
--   **Formalization Note** The paper says "as the partition becomes finer" without naming a limit; the anchor $\bar x$ with a nondegenerate, level-bounded minimizer, and regions in a ball around it, pin the limit down and make the little-$o$ uniform as $f_0$ moves with $R_0$. The bound carries the factor $p_0\le1$, so it implies the printed $o(\mathcal D_0^2)$; the printed form alone would follow from crude $O(p_0\mathcal D_0^2)$ bounds on both terms whenever $p_0\to0$, and is not the content of the theorem. Condition 4 ("twice Lipschitz-continuously differentiable in $x$") is replaced by $x$-Lipschitz bounds on $\bar c$ and its first two $z$-derivatives, which is what the proof uses. Condition 3's minimizer is read as depending on $t$ (the page names it $z_0$ for every $t$, which would force $\nabla f_j(z_0)=0$ and make the criterion zero). The minima in $\mathcal C^{\mathrm{oracle}}$ are real infima; condition 3 at $t=1$ makes them attained.
-- source:
--   Kallus & Mao, arXiv:2008.07473v6, pp. 9–10, Theorem 2 (proof p. 81)

import Mathlib
import Definitions.Def_StochOptForest_ApxRisk_Model

namespace StochOptForest.ApxRisk

open MeasureTheory

theorem theorem_2 {p d : ℕ} (μ : Measure (Xp p)) [IsProbabilityMeasure μ]
    (cbar : Xp p → Ed d → ℝ) (L : ℝ) (xbar : Xp p) (zbar : Ed d)
    (hC2 : ∀ x, ContDiff ℝ 2 (cbar x)) (hLip : XLipschitz cbar L)
    (hanchor : IsUniqueMin (cbar xbar) zbar) (hpd : PosDefAt (cbar xbar) zbar)
    (hlev : ∃ α : ℝ, cbar xbar zbar < α ∧ Bornology.IsBounded {z | cbar xbar z ≤ α}) :
    ∀ ε > 0, ∃ δ > 0, ∀ R0 R1 R2 : Set (Xp p),
      MeasurableSet R1 → MeasurableSet R2 → Disjoint R1 R2 → R0 = R1 ∪ R2 →
      R0 ⊆ Metric.ball xbar δ → 0 < μ R1 → 0 < μ R2 →
      -- conditions 1–3 of Theorem 2, for both j = 1, 2
      (∀ Rj ∈ ({R1, R2} : Set (Set (Xp p))),
        -- condition 1: f₀ and f_j are twice continuously differentiable
        (ContDiff ℝ 2 (regionAvg μ cbar R0) ∧ ContDiff ℝ 2 (regionAvg μ cbar Rj)) ∧
        -- condition 2: the sublevel sets are nonempty and uniformly bounded for t ∈ [0,1]
        (∃ α : ℝ, ∃ C : Set (Ed d), Bornology.IsBounded C ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1,
          {z | regionAvg μ cbar R0 z + t * (regionAvg μ cbar Rj z - regionAvg μ cbar R0 z) ≤ α}.Nonempty ∧
          {z | regionAvg μ cbar R0 z + t * (regionAvg μ cbar Rj z - regionAvg μ cbar R0 z) ≤ α} ⊆ C) ∧
        -- condition 3: a unique minimizer with positive definite Hessian for every t ∈ [0,1]
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ zt : Ed d,
          IsUniqueMin (fun z => regionAvg μ cbar R0 z + t * (regionAvg μ cbar Rj z - regionAvg μ cbar R0 z)) zt ∧
          PosDefAt (fun z => regionAvg μ cbar R0 z + t * (regionAvg μ cbar Rj z - regionAvg μ cbar R0 z)) zt)) →
      ∀ z0 : Ed d, IsUniqueMin (regionAvg μ cbar R0) z0 →
        |oracleCrit μ cbar R1 R2 - regionProb μ R0 * regionAvg μ cbar R0 z0
            - apxRiskCrit μ cbar R0 R1 R2 z0|
          ≤ ε * regionProb μ R0 * Metric.diam R0 ^ 2 := by sorry

end StochOptForest.ApxRisk
