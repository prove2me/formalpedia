-- Prove2me | Theorems.Thm_RoughSurfaceScattering_harmonic_gradient_estimate_R3
-- name    : RoughSurfaceScattering.harmonic_gradient_estimate_R3
-- status  : Open
-- author  : @もち
-- created : 2026-11-24T06:11:44.801099+00:00
-- url     : https://prove2.me/theorems/524851c5-fada-4ffa-94f5-f16bac105557
-- title:
--   Gradient estimate $\|Df(z)\|\le\frac3r\sup_{\overline B(z,r)}\|f\|$ for harmonic functions on $\mathbb R^3$
-- statement:
--   Let $F$ be a real Banach space, $U\subseteq\mathbb R^3$ open, and $f:U\to F$ harmonic on $U$. If $\overline B(z,r)\subseteq U$ with $r>0$ and $\|f\|\le K$ on $\overline B(z,r)$, then
--
--   $$\|Df(z)\|\le\frac3r\,K .$$
--
--   For a unit vector $v$, the directional derivative $\partial_vf$ is harmonic. By the mean-value property it equals its average over $B(z,r)$, which by the divergence theorem is $\frac1{|B_r|}\int_{\partial B_r}f\,(v\cdot\nu)\,dS$. Its norm is therefore at most $\frac{|\partial B_r|}{|B_r|}K=\frac3rK$. Applied to the derivatives $D^nf$ on nested balls, this gives the factorial Cauchy estimates.
--
--   **Formalization Note** $\|Df(z)\|$ is the operator norm of `fderiv ℝ f z`. Values in an arbitrary Banach space are allowed so that the estimate applies to `iteratedFDeriv`.
-- source:
--   L. C. Evans, Partial Differential Equations, 2nd ed., §2.2.3, Theorem 7 (estimates on derivatives, case k = 1), in sup-norm form: |∂_i u(x0)| ≤ (n/r) sup_{∂B(x0,r)} |u| from the mean-value property of ∂_i u and the divergence theorem.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem harmonic_gradient_estimate_R3 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (f : EuclideanSpace ℝ (Fin 3) → F)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : IsOpen U)
    (hf : InnerProductSpace.HarmonicOnNhd f U) (z : EuclideanSpace ℝ (Fin 3)) (r : ℝ)
    (hr : 0 < r) (hzr : Metric.closedBall z r ⊆ U) (K : ℝ)
    (hK : ∀ w ∈ Metric.closedBall z r, ‖f w‖ ≤ K) :
    ‖fderiv ℝ f z‖ ≤ 3 / r * K := by sorry

end RoughSurfaceScattering
