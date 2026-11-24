-- Prove2me | Theorems.Thm_RoughSurfaceScattering_h1Norm_sub_le
-- name    : RoughSurfaceScattering.h1Norm_sub_le
-- status  : Proved
-- author  : @もち
-- created : 2026-11-24T03:52:41.986294+00:00
-- url     : https://prove2.me/theorems/ad3e8b6f-1332-440d-bd19-2c942f1d7a08
-- title:
--   Triangle inequality for the $H^1(D)$ norm of $C^1$ functions
-- statement:
--   Let $D\subseteq\mathbb R^2$ be open and let $v,w:D\to\mathbb C$ be continuously differentiable on $D$. With
--
--   $$\|u\|_{H^1(D)}=\Big(\int_D|u|^2+|\partial_1u|^2+|\partial_2u|^2\,dx\Big)^{1/2}\in[0,\infty],$$
--
--   the triangle inequality holds:
--
--   $$\|v-w\|_{H^1(D)}\le\|v\|_{H^1(D)}+\|w\|_{H^1(D)} .$$
--
--   This is the Minkowski inequality for $H^1(D)$, used whenever the singular part of a field is split off, as in Theorems 5.2 and 5.3 and in the proof of Theorem 6.1.
--
--   **Formalization Note** The norm is the platform's `h1Norm`, computed from the Fréchet derivative, with value $\infty$ when the integral diverges. The $C^1$ hypothesis makes the derivatives of $v-w$ the differences of the derivatives and makes all integrands measurable on $D$.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Sections 5–6 (the H^1(D_0) norm used in Theorems 5.2, 5.3 and in the proof of Theorem 6.1, PDF pp. 17–25); standard Minkowski inequality for H^1(D) = W^{1,2}(D).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem h1Norm_sub_le (D : Set R2) (hD : IsOpen D) (v w : R2 → ℂ)
    (hv : ContDiffOn ℝ 1 v D) (hw : ContDiffOn ℝ 1 w D) :
    h1Norm D (fun x => v x - w x) ≤ h1Norm D v + h1Norm D w := by sorry

end RoughSurfaceScattering
