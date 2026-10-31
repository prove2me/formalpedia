-- Prove2me | Theorems.Thm_StochOptForest_ApxRisk_region_avg_derivatives
-- name    : StochOptForest.ApxRisk.region_avg_derivatives
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:28:58.30106+00:00
-- url     : https://prove2.me/theorems/05f2435f-12dd-4be2-9a00-a3b6cfc4e9fa
-- title:
--   Example 5, p. 11 — region averages are C² with ∇f_j = E[∇c̄ | X ∈ R_j] and ∇²f_j = E[∇²c̄ | X ∈ R_j]
-- statement:
--   Let $\mu$ be a probability measure on $\mathbb R^p$ and $\bar c(x,z)$ a regression cost such that
--
--   1. for every $x$, $z\mapsto\bar c(x,z)$ is twice continuously differentiable;
--   2. $\bar c$ is $x$-Lipschitz with constant $L$: $\bar c(\cdot,z)$, $\nabla_z\bar c(\cdot,z)$ and $\nabla_z^2\bar c(\cdot,z)$ are $L$-Lipschitz in $x$, uniformly in $z$.
--
--   Let $R\subseteq\mathbb R^p$ be a bounded measurable region with $\mu(R)>0$ and $f_R(z)=\mu(R)^{-1}\int_R\bar c(x,z)\,d\mu(x)$. Then $f_R$ is twice continuously differentiable and, for every $z$,
--   $$\nabla f_R(z)=\frac{1}{\mu(R)}\int_R\nabla_z\bar c(x,z)\,d\mu(x),\qquad \nabla^2 f_R(z)=\frac{1}{\mu(R)}\int_R\nabla_z^2\bar c(x,z)\,d\mu(x).$$
--
--   This is condition 1 of Theorems 1 and 2 for every region, together with the formulas for the gradients and Hessians that enter the approximate criteria.
--
--   **Formalization Note** Example 5 exchanges derivative and the expectation over $Y$ for a smooth cost $c(z;y)$. Here the same exchange is made for the expectation over $X\in R$ of the regression cost $\bar c$, which is the form the model uses; the Lipschitz hypothesis on a bounded region supplies the domination that Example 5 asks for.
-- source:
--   Kallus & Mao, arXiv:2008.07473v6, p. 11, Example 5

import Mathlib
import Definitions.Def_StochOptForest_ApxRisk_Model

namespace StochOptForest.ApxRisk

open MeasureTheory

theorem region_avg_derivatives {p d : ℕ} (μ : Measure (Xp p)) [IsProbabilityMeasure μ]
    (cbar : Xp p → Ed d → ℝ) (L : ℝ) (hC2 : ∀ x, ContDiff ℝ 2 (cbar x))
    (hLip : XLipschitz cbar L) (R : Set (Xp p)) (hR : MeasurableSet R)
    (hRb : Bornology.IsBounded R) (hpos : 0 < μ R) :
    ContDiff ℝ 2 (regionAvg μ cbar R) ∧
    (∀ z, gradient (regionAvg μ cbar R) z = (μ R).toReal⁻¹ • ∫ x in R, gradient (cbar x) z ∂μ) ∧
    (∀ z, hess (regionAvg μ cbar R) z = (μ R).toReal⁻¹ • ∫ x in R, hess (cbar x) z ∂μ) := by sorry

end StochOptForest.ApxRisk
