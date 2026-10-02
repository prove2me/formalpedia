-- Prove2me | Theorems.Thm_TegmarkDimensionality_no_stable_orbits_above_three_dims
-- name    : TegmarkDimensionality.no_stable_orbits_above_three_dims
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-02T02:40:40.571473+00:00
-- url     : https://prove2.me/theorems/ae495a1b-cc9d-4d1a-8ac3-2873d906b6c4
-- title:
--   No stable orbits in the two-body problem for $n>3$
-- statement:
--   Let $n>3$ be the number of space dimensions. Consider a particle of reduced mass $\mu>0$ moving in the attractive potential $V(r)=-k\,r^{2-n}$, $k>0$, with angular momentum $L\in\mathbb R$. Its radial motion is governed by the effective potential
--   $$U(r)=\frac{L^2}{2\mu r^2}-k\,r^{2-n},\qquad r>0.$$
--   Then $U$ has **no strict local minimum** at any radius $r_0>0$. In other words, there is no $r_0>0$ such that $U(r_0)<U(r)$ for all $r\neq r_0$ sufficiently close to $r_0$.
--
--   Strict local minima of $U$ are exactly the stable circular orbits, so the two-body problem has no stable orbits when $n>3$. This is in contrast with $n=3$, treated in the next milestone.
--
--   **Formalization Note** A strict local minimum is used because for $n=4$ and $L^2=2\mu k$ the potential $U$ is constant, and every radius is then a non-strict, neutrally unstable critical point.
-- source:
--   M. Tegmark, *On the dimensionality of spacetime*, Class. Quantum Grav. 14 (1997) L69–L75, https://doi.org/10.1088/0264-9381/14/4/002, p. L70, first paragraph ('When n > 3, the two-body problem no longer has any stable orbits as solutions'), citing Büchel 1963 and Freeman 1969

import Mathlib
open Filter Topology

namespace TegmarkDimensionality

/-- For `n > 3` space dimensions the attractive two-body problem with potential
`-k r^{2-n}` has no stable orbit: the effective radial potential
`U(r) = L²/(2 μ r²) - k r^{2-n}` has no strict local minimum at any radius `r₀ > 0`. -/
theorem no_stable_orbits_above_three_dims (n : ℕ) (hn : 3 < n)
    (μ k L : ℝ) (hμ : 0 < μ) (hk : 0 < k) :
    ¬ ∃ r₀ : ℝ, 0 < r₀ ∧
      ∀ᶠ r in 𝓝[≠] r₀,
        L ^ 2 / (2 * μ * r₀ ^ 2) - k * r₀ ^ ((2 : ℝ) - n) <
          L ^ 2 / (2 * μ * r ^ 2) - k * r ^ ((2 : ℝ) - n) := by sorry

end TegmarkDimensionality
