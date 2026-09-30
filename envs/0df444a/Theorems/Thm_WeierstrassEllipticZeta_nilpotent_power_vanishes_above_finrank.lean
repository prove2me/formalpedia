-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_nilpotent_power_vanishes_above_finrank
-- name    : WeierstrassEllipticZeta.nilpotent_power_vanishes_above_finrank
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-10T21:30:22.825152+00:00
-- url     : https://prove2.me/theorems/1b3ec1f4-d7e6-4ae5-81d0-b0de7f4e1e9f
-- title:
--   Nilpotent powers vanish at and above the algebra dimension
-- statement:
--   Let $K$ be a field and let $B$ be a finite-dimensional unital $K$-algebra, not necessarily commutative. If $x\in B$ is nilpotent, then
--   $$
--   x^N=0\qquad\text{for every integer }N\ge\dim_K B.
--   $$
--   In particular, the dimension of $B$ is a vanishing exponent. The assertion also includes the zero algebra, where the dimension is zero and $x^0=1_B=0_B$.
-- source:
--   Derived algebra lemma for the approach associated with Senthil Kumar K (2026), Appendix A and Theorem A.2, https://doi.org/10.1017/S001309152610145X. This lemma is proved here and is not quoted from the article. A nilpotent element in a finite-dimensional algebra over a field has every power at least the algebra dimension equal to zero. It follows from the characteristic polynomial of nilpotent left multiplication and Cayley-Hamilton. The algebra need not be commutative. No new definitions or platform theorem dependencies.

import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.Algebra.Algebra.Bilinear

theorem WeierstrassEllipticZeta.nilpotent_power_vanishes_above_finrank
    (K B : Type*) [Field K] [Ring B] [Algebra K B] [FiniteDimensional K B]
    (x : B) (hx : IsNilpotent x) :
    ∀ N : ℕ, Module.finrank K B ≤ N → x ^ N = 0 := by sorry
