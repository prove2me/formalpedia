-- Prove2me | Theorems.Thm_WeierstrassCurve_isElliptic_legendreCurve_iff
-- name    : WeierstrassCurve.isElliptic_legendreCurve_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/be67e6ac-e17f-5377-af86-1eb78d097499
-- title:
--   The Legendre curve is elliptic iff t≠ 0,1
-- statement:
--   Let $K$ be a field in which $2\neq 0$, and let $t\in K$. Write $E_t$ for the Weierstrass curve `legendreCurve t` over $K$, defined by the coefficient tuple $(a_1,a_2,a_3,a_4,a_6)=(0,-(1+t),0,t,0)$, i.e. the affine model $y^2=x^3-(1+t)x^2+tx=x(x-1)(x-t)$. The theorem asserts that $E_t$ satisfies Mathlib's predicate `IsElliptic`, i.e. that its discriminant $\Delta(E_t)$ is a unit of $K$, if and only if both $t\neq 0$ and $t\neq 1$. Since $K$ is a field, being a unit is the same as being nonzero, and the statement is thus the nonvanishing criterion for $\Delta(E_t)=16\,t^2(t-1)^2$; the hypothesis $2\neq 0$ is what makes the factor $16$ invertible and so is needed only for the implication from $t\neq 0$, $t\neq 1$ to ellipticity.
--
--   This is the standard smoothness criterion for the Legendre family $y^2=x(x-1)(x-t)$ in characteristic different from $2$. It licenses treating the Legendre curves as genuine elliptic curves, and is used in the Hasse-invariant description of the supersingular locus, for instance in the identification of supersingular $j$-invariants with the image of $t\mapsto j(E_t)$ and in the resulting factorisation statements for the Deuring polynomial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_isElliptic_legendreCurve_iff.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_HasseInvariant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve

theorem WeierstrassCurve.isElliptic_legendreCurve_iff {K : Type*} [Field K] (t : K) (h2 : (2 : K) ≠ 0) :
    (legendreCurve t).IsElliptic ↔ t ≠ 0 ∧ t ≠ 1 := by sorry
