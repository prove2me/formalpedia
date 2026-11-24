-- Prove2me | Theorems.Thm_RoughSurfaceScattering_weak_deriv_removable_point
-- name    : RoughSurfaceScattering.weak_deriv_removable_point
-- status  : Open
-- author  : @もち
-- created : 2026-11-24T15:55:49.675807+00:00
-- url     : https://prove2.me/theorems/fc08004f-80a0-4e25-beeb-d2530a356e43
-- title:
--   In the plane a point is removable for weak derivatives of continuous functions
-- statement:
--   Let $U\subseteq\mathbb R^2$ be open, $y\in\mathbb R^2$, and $v\in\mathbb R^2$. Let $g:U\to\mathbb C$ be continuous on $U$ and differentiable at every point of $U\setminus\{y\}$, with $\partial_vg\in L^1(U)$. Then the classical derivative is the weak derivative:
--
--   $$\int_Ug\,\partial_v\varphi\,dx=-\int_U\partial_vg\,\varphi\,dx\qquad\text{for all }\varphi\in C_c^\infty(U).$$
--
--   In dimension two a single point has zero capacity. Cutting $\varphi$ off near $y$ by $\chi(|x-y|/\varepsilon)$, the error term is bounded by $\sup|g|\cdot\|\nabla\chi_\varepsilon\|_{L^1}=O(\varepsilon)$, while the remaining part converges by dominated convergence. This lemma identifies weak second derivatives of functions whose classical second derivatives are singular at one point, such as differences of fundamental solutions.
--
--   **Formalization Note** Weak derivatives are the platform's `IsWeakDeriv`, tested against real-valued smooth compactly supported $\varphi$. The value of `fderiv` at the exceptional point is irrelevant, since a point is a null set.
-- source:
--   Classical removability of points for Sobolev functions in dimension ≥ 2 (a point has zero capacity); e.g. L. C. Evans and R. F. Gariepy, Measure Theory and Fine Properties of Functions, §4.7. Used for Lemma 5.1 of C. Wu and J. Yang, arXiv:2406.06129v2, PDF p. 17.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem weak_deriv_removable_point (U : Set R2) (hU : IsOpen U) (y : R2) (g : R2 → ℂ)
    (hc : ContinuousOn g U) (hd : ∀ x ∈ U, x ≠ y → DifferentiableAt ℝ g x) (v : R2)
    (hint : IntegrableOn (fun x => fderiv ℝ g x v) U) :
    IsWeakDeriv U g v (fun x => fderiv ℝ g x v) := by sorry

end RoughSurfaceScattering
