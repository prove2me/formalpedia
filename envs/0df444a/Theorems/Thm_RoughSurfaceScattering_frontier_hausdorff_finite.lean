-- Prove2me | Theorems.Thm_RoughSurfaceScattering_frontier_hausdorff_finite
-- name    : RoughSurfaceScattering.frontier_hausdorff_finite
-- status  : Proved
-- author  : @もち
-- created : 2026-11-24T05:09:26.382866+00:00
-- url     : https://prove2.me/theorems/046cc761-b00a-48cd-9c96-915febae135a
-- title:
--   The boundary of a bounded $C^{2,\lambda}$ domain has finite length
-- statement:
--   Let $D\subseteq\mathbb R^2$ be a bounded $C^{2,\lambda}$ domain: a bounded connected open set which, near each boundary point $p$ and in suitable rotated or reflected coordinates centred at $p$, is the region below the graph of a $C^{2,\lambda}$ function. Then its boundary has finite one-dimensional Hausdorff measure:
--
--   $$\mathcal H^1(\partial D)<\infty .$$
--
--   The boundary is compact. It is covered by finitely many coordinate patches, in each of which it is the graph of a $C^1$ function over a bounded interval, hence a Lipschitz image of an interval. So $\partial D$ is a curve of finite length, and arc length $ds=\mathcal H^1\llcorner\partial D$ is a finite measure. This is what makes boundary integrals such as the correction term $v_j$ of Theorem 5.3 well defined for bounded densities.
--
--   **Formalization Note** $\mathcal H^1$ is Mathlib's `Measure.hausdorffMeasure 1` on $\mathbb R^2$, and the domain class is the platform's `IsC2LambdaDomain`.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Theorem 5.3, PDF p. 21 (the boundary integral over ∂D_0 with the outward unit normal n(y) of the bounded C^{2,λ} domain D_0 and arc length ds(y)); standard properties of bounded C^{2,λ} domains.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem frontier_hausdorff_finite (lam : ℝ) (D : Set R2) (hD : IsC2LambdaDomain lam D) :
    (Measure.hausdorffMeasure 1 : Measure R2) (frontier D) ≠ ⊤ := by sorry

end RoughSurfaceScattering
