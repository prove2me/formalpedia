-- Prove2me | Theorems.Thm_TegmarkDimensionality_stable_orbit_three_dims
-- name    : TegmarkDimensionality.stable_orbit_three_dims
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T02:50:39.1482+00:00
-- url     : https://prove2.me/theorems/8a1f7c30-4bfc-402d-ae85-3f33feb4ae2c
-- title:
--   Stable circular orbits exist for $n=3$
-- statement:
--   Let $\mu>0$, $k>0$ and $L\neq0$. The effective potential of the three-dimensional Kepler problem,
--   $$U(r)=\frac{L^2}{2\mu r^2}-\frac{k}{r},$$
--   has a strict local minimum at some $r_0>0$. That is, there is $r_0>0$ with $U(r_0)<U(r)$ for all $r\neq r_0$ near $r_0$.
--
--   So for $n=3$ the two-body problem has stable (circular, and nearby elliptic) orbits, unlike the case $n>3$.
-- source:
--   M. Tegmark, *On the dimensionality of spacetime*, Class. Quantum Grav. 14 (1997) L69–L75, https://doi.org/10.1088/0264-9381/14/4/002, p. L70–L71 ('the familiar case, n = 3, which gives either stable elliptic orbits or non-bound parabolic and hyperbolic orbits')

import Mathlib
open Filter Topology

namespace TegmarkDimensionality

/-- In `n = 3` space dimensions, with the inverse-square attraction (potential `-k/r`) and
nonzero angular momentum, the effective radial potential `U(r) = L²/(2 μ r²) - k/r` has a
strict local minimum at some radius `r₀ > 0` (a stable circular orbit). -/
theorem stable_orbit_three_dims (μ k L : ℝ) (hμ : 0 < μ) (hk : 0 < k) (hL : L ≠ 0) :
    ∃ r₀ : ℝ, 0 < r₀ ∧
      ∀ᶠ r in 𝓝[≠] r₀,
        L ^ 2 / (2 * μ * r₀ ^ 2) - k / r₀ < L ^ 2 / (2 * μ * r ^ 2) - k / r := by sorry

end TegmarkDimensionality
