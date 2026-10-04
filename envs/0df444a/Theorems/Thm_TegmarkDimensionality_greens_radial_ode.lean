-- Prove2me | Theorems.Thm_TegmarkDimensionality_greens_radial_ode
-- name    : TegmarkDimensionality.greens_radial_ode
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T01:16:58.033983+00:00
-- url     : https://prove2.me/theorems/9c56d9f8-356c-4af3-9d0f-f9fbbdac3124
-- title:
--   Radial ODE for the Green profile $r^{2-n}$
-- statement:
--   For integers $n>2$ and real $r>0$, writing $g(t)=t^{2-n}$, the radial Laplace equation in $n$ dimensions,
--   $$g''(r)+\frac{n-1}{r}g'(r)=0,$$
--   holds. This is the scalar ODE obtained by writing the Laplacian of a radial function in terms of $g$ and $r$.
-- source:
--   M. Tegmark, On the dimensionality of spacetime, Class. Quantum Grav. 14 (1997) L69–L75, p. L70 (Poisson equation); classical radial Laplacian computation

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace TegmarkDimensionality

/-- For `n > 2`, the radial profile `g(r)=r^{2-n}` satisfies the harmonic ODE
`g'' + (n-1)g'/r = 0` for `r > 0`. This is the one-variable identity behind
the Green function milestone. -/
theorem greens_radial_ode (n : ℕ) (hn : 2 < n) (r : ℝ) (hr : 0 < r) :
    let g := fun t : ℝ => t ^ ((2 : ℝ) - n)
    deriv (deriv g) r + ((n : ℝ) - 1) / r * deriv g r = 0 := by sorry

end TegmarkDimensionality
