-- Prove2me | Theorems.Thm_WeierstrassCurve_map_fullKernelQuotient_mapPoint
-- name    : WeierstrassCurve.map_fullKernelQuotient_mapPoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/f69c3244-ff45-59b7-a313-8e8e22940be4
-- title:
--   Full-kernel Vélu quotient commutes with base change
-- statement:
--   Let $F$ and $K$ be fields, $f : F \to K$ a ring homomorphism, $W$ a Weierstrass curve over $F$ given by coefficients $a_1,\dots,a_6$, $Q$ a point of the associated affine curve `W.toAffine` (either the point at infinity or an affine nonsingular point), and $N$ a natural number. Here `W.fullKernelQuotient Q N` is the Weierstrass curve obtained from $W$ by the substitution $a_1,a_2,a_3$ unchanged, $a_4 \mapsto a_4 - 5t$, $a_6 \mapsto a_6 - b_2 t - 7w$, where $t = \sum_P g_x(x_P,y_P)$ and $w = \sum_P \bigl(x_P\,g_x(x_P,y_P) - y_P\,g_y(x_P,y_P)\bigr)$, with $g_x(x,y) = 3x^2 + 2a_2x + a_4 - a_1y$ and $g_y(x,y) = -(2y + a_1x + a_3)$, and the sums run over the finite set of pairs `(k • Q).coordsOrZero` for $1 \le k \le N-1$ (truncated subtraction, so the set is empty for $N \le 1$; the point at infinity contributes $(0,0)$, and repeated pairs occur only once). Writing `mapPoint f` for the map on points sending the point at infinity to itself and an affine point $(x,y)$ to $(f(x),f(y))$, the assertion is that the full-kernel quotient at level $N$ of the base-changed curve `W.map f` by the point `mapPoint f Q` equals the base change along $f$ of `W.fullKernelQuotient Q N`.
--
--   This is the base-change compatibility of the explicit Vélu-type quotient construction attached to a point and a level, in the form of an equality of Weierstrass curves over $K$. It is used in the analysis of the modular curve, where the quotient construction must be compared before and after reduction, in [`ModularCurve.exists_equivariant_torsion_reduction_ofJ_evalAt_fullKernelQuotient_j_ord_mul_natCard`](thm.html#ModularCurve.exists_equivariant_torsion_reduction_ofJ_evalAt_fullKernelQuotient_j_ord_mul_natCard) and in [`ModularCurve.ord_sub_mul_natCard_stabilizer_zmultiples_reduceHom_eq_ramificationIndexAlong_mul_natCard_stabilizer_fullKernelQuotient`](thm.html#ModularCurve.ord_sub_mul_natCard_stabilizer_zmultiples_reduceHom_eq_ramificationIndexAlong_mul_natCard_stabilizer_fullKernelQuotient).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_map_fullKernelQuotient_mapPoint.lean

import Definitions.Def_WeierstrassCurve_FullKernelQuotient
import Definitions.Def_WeierstrassCurve_MapPoint

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.map_fullKernelQuotient_mapPoint {F K : Type*} [Field F] [Field K]
    [DecidableEq F] [DecidableEq K] (W : WeierstrassCurve F) (f : F →+* K) (Q : W.toAffine.Point)
    (N : ℕ) :
    (W.map f).fullKernelQuotient (mapPoint f Q) N = (W.fullKernelQuotient Q N).map f := by sorry
