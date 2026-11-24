-- Prove2me | Theorems.Thm_RoughSurfaceScattering_outwardNormal_continuousOn
-- name    : RoughSurfaceScattering.outwardNormal_continuousOn
-- status  : Open
-- author  : @もち
-- created : 2026-11-24T05:09:26.225813+00:00
-- url     : https://prove2.me/theorems/d0240d35-d1d2-4228-b620-ca6c5c37977b
-- title:
--   The outward unit normal of a $C^{2,\lambda}$ domain is continuous on the boundary
-- statement:
--   Let $D\subseteq\mathbb R^2$ be a bounded $C^{2,\lambda}$ domain and let $n(y)$, $y\in\partial D$, denote its outward unit normal. Then
--
--   $$y\mapsto n(y)\quad\text{is continuous on }\partial D .$$
--
--   In a coordinate patch where $D$ lies below the graph of a $C^{2,\lambda}$ function $g$, the vector obtained by rotating $(-g'(t),1)/\sqrt{1+g'(t)^2}$ back to the original coordinates is an outward unit normal at the boundary point over $t$. The outward normal at a boundary point is unique, because two distinct unit vectors cannot both separate the inside from the outside cone-wise. So $n$ agrees on the patch with this formula, which is continuous in $t$ since $g'$ is.
--
--   **Formalization Note** $n$ is the platform's `outwardNormal D`, defined by choice among the unit vectors $\nu$ satisfying the cone condition `IsOutwardNormal D y ν`. The statement includes that such a vector exists and is unique at every boundary point of a $C^{2,\lambda}$ domain.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Theorem 5.3, PDF p. 21 (the boundary integral over ∂D_0 with the outward unit normal n(y) of the bounded C^{2,λ} domain D_0 and arc length ds(y)); standard properties of bounded C^{2,λ} domains.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem outwardNormal_continuousOn (lam : ℝ) (D : Set R2) (hD : IsC2LambdaDomain lam D) :
    ContinuousOn (outwardNormal D) (frontier D) := by sorry

end RoughSurfaceScattering
