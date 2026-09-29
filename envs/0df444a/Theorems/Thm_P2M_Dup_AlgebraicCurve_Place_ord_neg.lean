-- Prove2me | Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_neg
-- name    : P2M.Dup.AlgebraicCurve.Place.ord_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/8c0b10a2-5676-5352-854d-dc714c96fb0c
-- title:
--   Invariance of ordᵥ under negation
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F$ over $K$ in the sense of the project's structure [`AlgebraicCurve.Place`](def/AlgebraicCurve_DivisorClassGroup.html#L22): a valuation subring of $F$ containing the image of $K$ under the structure map, distinct from all of $F$, and a principal ideal ring. Attached to $v$ is the valuation [`AlgebraicCurve.Place.adicValuation`](def/AlgebraicCurve_DivisorClassGroup.html#L102), the $\mathbb{Z}^{m0}$-valued adic valuation of the height one prime of $v$, and the integer-valued order function $\operatorname{ord}_v(f) = -\log(v_{\mathrm{adic}}(f))$, where $\log$ is the `WithZero` logarithm (so that the value $0$ of the valuation, in particular at $f = 0$, contributes $\operatorname{ord}_v = 0$). The theorem asserts that for every $f \in F$, with no further hypotheses on $f$ and in particular with no assumption on the characteristic, $\operatorname{ord}_v(-f) = \operatorname{ord}_v(f)$; the case $f = 0$ is included, both sides then being $0$ by the stated convention.
--
--   A routine ultrametric normalisation fact for the order function of a place, recording that $\operatorname{ord}_v$ is insensitive to sign. It is used throughout the divisor-theoretic development of curves, for instance in the statements about the existence of elements with prescribed valuations of differences and in the computations of orders of differentials.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_ord_neg.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_PlacesOverDVR

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem P2M.Dup.AlgebraicCurve.Place.ord_neg {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F) (f : F) :
    v.ord (-f) = v.ord f := by sorry
