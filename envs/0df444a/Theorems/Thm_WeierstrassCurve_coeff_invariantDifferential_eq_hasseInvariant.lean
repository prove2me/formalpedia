-- Prove2me | Theorems.Thm_WeierstrassCurve_coeff_invariantDifferential_eq_hasseInvariant
-- name    : WeierstrassCurve.coeff_invariantDifferential_eq_hasseInvariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/6abf42d6-d674-53aa-ba05-c8657fd01657
-- title:
--   Hasse invariant as a coefficient of the invariant differential
-- statement:
--   Let $R$ be a commutative ring of prime characteristic $q$ with $q \neq 2$, and let $W$ be a Weierstrass curve over $R$ with coefficients $a_1,a_2,a_3,a_4,a_6$. Let $x, y, \omega$ be Laurent series over $R$ (elements of `LaurentSeries R`, i.e. Hahn series over $\mathbb{Z}$ with the usual summability) subject to: the Weierstrass relation $y^2 + a_1 x y + a_3 y = x^3 + a_2 x^2 + a_4 x + a_6$, where the $a_i$ enter as constant series; $x$ has coefficient $1$ in degree $-2$ and vanishing coefficients in all degrees $< -2$; $y$ has coefficient $-1$ in degree $-3$ and vanishing coefficients in all degrees $< -3$; and $\omega \cdot (2y + a_1 x + a_3)$ equals the formal derivative of $x$. The conclusion is that the coefficient of $\omega$ in degree $q - 1$ (as an integer) equals $W$'s Hasse invariant at $q$, defined as the coefficient of $X^{q-1}$ in the $\lfloor (q-1)/2 \rfloor$-th power of the polynomial underlying the two-torsion cubic $4X^3 + b_2 X^2 + 2b_4 X + b_6$ of $W$.
--
--   This is Katz's first description of the Hasse invariant, read for an arbitrary formal point $(x,y)$ with the standard leading behaviour rather than for the formal group parametrisation: $\omega\,dz = dx/(2y + a_1x + a_3)$ is the invariant differential, and its $z^{q-1}$-coefficient recovers the Hasse invariant in characteristic $q$. It is used to identify the Hasse invariant with coefficients of Tate-curve type series expansions, via [`WeierstrassCurve.exists_coeff_nthSeries_eq_mul_hasseInvariant`](thm.html#WeierstrassCurve.exists_coeff_nthSeries_eq_mul_hasseInvariant) and [`WeierstrassCurve.hasseInvariant_tatePowerSeries_map`](thm.html#WeierstrassCurve.hasseInvariant_tatePowerSeries_map).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_coeff_invariantDifferential_eq_hasseInvariant.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_HasseInvariant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

theorem WeierstrassCurve.coeff_invariantDifferential_eq_hasseInvariant
    {R : Type*} [CommRing R] (q : ℕ) [Fact q.Prime] [CharP R q] (hq : q ≠ 2)
    (W : WeierstrassCurve R) (x y ω : LaurentSeries R)
    (heq : y ^ 2 + HahnSeries.C W.a₁ * x * y + HahnSeries.C W.a₃ * y
      = x ^ 3 + HahnSeries.C W.a₂ * x ^ 2 + HahnSeries.C W.a₄ * x + HahnSeries.C W.a₆)
    (hx2 : x.coeff (-2) = 1) (hx : ∀ n < -2, x.coeff n = 0)
    (hy3 : y.coeff (-3) = -1) (hy : ∀ n < -3, y.coeff n = 0)
    (hω : ω * (2 * y + HahnSeries.C W.a₁ * x + HahnSeries.C W.a₃) = LaurentSeries.derivative R x) :
    ω.coeff ((q : ℤ) - 1) = W.hasseInvariant q := by sorry
