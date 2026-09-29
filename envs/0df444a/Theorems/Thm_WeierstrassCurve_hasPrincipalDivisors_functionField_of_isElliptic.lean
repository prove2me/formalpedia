-- Prove2me | Theorems.Thm_WeierstrassCurve_hasPrincipalDivisors_functionField_of_isElliptic
-- name    : WeierstrassCurve.hasPrincipalDivisors_functionField_of_isElliptic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/afdd6205-e24d-55d6-a536-79f8233d1c5d
-- title:
--   Principal divisors on an elliptic function field, any characteristic
-- statement:
--   Let $F$ be a field and let $W$ be a Weierstrass curve over $F$ which is elliptic, i.e. whose discriminant $\Delta$ is a unit of $F$. Write $F(W)$ for the function field `W.toAffine.FunctionField` of the associated affine Weierstrass curve. The assertion is that the class [`AlgebraicCurve.HasPrincipalDivisors F F(W)`](def/AlgebraicCurve_DivisorClassGroup.html#L217) holds for this extension, that is: for every $f \in F(W)$ with $f \neq 0$ there is a divisor $D$, meaning a finitely supported function from the places of $F(W)$ over $F$ to $\mathbb{Z}$, such that $D(v) = \operatorname{ord}_v(f)$ for every place $v$, and such that $\deg D = \sum_v D(v)\cdot \deg(v) = 0$. Here a place of $F(W)$ over $F$ is a valuation subring of $F(W)$ that contains the image of $F$, is not the whole field, and is a principal ideal ring. Existence of such a $D$ thus packages two statements at once: the order function $v \mapsto \operatorname{ord}_v(f)$ has finite support on the set of places, and the resulting divisor of $f$ has degree zero.
--
--   This is the statement that the divisor of a nonzero function on an elliptic curve is a genuine divisor (finite support) of degree zero, with no hypothesis on the characteristic of $F$ beyond invertibility of the discriminant. It is the finiteness-and-degree input used by the isogeny and Vélu developments, for instance in the comparison of algebra homomorphisms of function fields through their effect on places of points and in the construction of isogenies with prescribed kernel.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_hasPrincipalDivisors_functionField_of_isElliptic.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.hasPrincipalDivisors_functionField_of_isElliptic
    {F : Type*} [Field F] (W : WeierstrassCurve F) [W.IsElliptic] :
    AlgebraicCurve.HasPrincipalDivisors F W.toAffine.FunctionField := by sorry
