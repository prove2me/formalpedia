-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_hasPrincipalDivisors_of_isAlgClosed
-- name    : WeierstrassCurve.Affine.hasPrincipalDivisors_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/01e9ef15-c33a-5810-9e0d-0e747a9fd8d7
-- title:
--   Principal divisors have degree zero on an elliptic curve
-- statement:
--   Let $F$ be an algebraically closed field and let $W$ be an affine Weierstrass curve over $F$ which is elliptic (i.e. satisfies `WeierstrassCurve.IsElliptic`). The assertion is that the function field $W$.`FunctionField`, viewed as an extension of $F$, satisfies the class [`AlgebraicCurve.HasPrincipalDivisors`](def/AlgebraicCurve_DivisorClassGroup.html#L217): for every $f$ in that function field with $f \neq 0$ there exists a finitely supported function $D$ from the places of $W$.`FunctionField` over $F$ to $\mathbb{Z}$ such that $D(v) = v.\mathrm{ord}(f)$ for *every* place $v$, and such that the degree of $D$, namely the sum $\sum_{v} D(v)\cdot \deg v$ over the (finite) support of $D$, is $0$. Here a place of $W$.`FunctionField` over $F$ is a valuation subring $O$ of the function field which contains the image of $F$ under the structure map, is not the whole field, and is a principal ideal ring, and $\mathrm{ord}$ and $\deg$ are the associated order and degree functions. Thus the statement packages two facts at once: a nonzero function has nonzero order at only finitely many places, and the resulting divisor has total degree zero.
--
--   This is the degree-zero property of principal divisors on a genus-one curve, the divisor-theoretic input behind the group law and the Abel–Jacobi description of points. It is used in the construction of the place-theoretic gate for the Abel theorem on Weierstrass curves and in the analysis of torsion on Tate curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_hasPrincipalDivisors_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.Affine.hasPrincipalDivisors_of_isAlgClosed {F : Type*} [Field F] [IsAlgClosed F] (W : WeierstrassCurve.Affine F) [W.IsElliptic] : AlgebraicCurve.HasPrincipalDivisors F W.FunctionField := by sorry
