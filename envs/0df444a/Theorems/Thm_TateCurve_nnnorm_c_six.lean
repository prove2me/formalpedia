-- Prove2me | Theorems.Thm_TateCurve_nnnorm_c_six
-- name    : TateCurve.nnnorm_c_six
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/380f775b-046f-51bc-be83-4428417d3e02
-- title:
--   The c₆-invariant of the Tate curve is a unit
-- statement:
--   Let $K$ be a nontrivially normed field whose norm is ultrametric and which is complete, and let $q \in K$ satisfy $\|q\|_+ < 1$ for the $\mathbb{R}_{\ge 0}$-valued norm. Here [`TateCurve.curve q`](def/TateCurve_QSeries.html#L185) is the Weierstrass curve over $K$ with coefficients $a_1 = 1$, $a_2 = a_3 = 0$, $a_4 =$ `a₄ q` and $a_6 =$ `a₆ q`, the latter two being the $q$-series functions of the Tate curve attached to $q$; they satisfy $\|$`a₄ q`$\|_+ \le \|q\|_+$ and $\|$`a₆ q`$\|_+ \le \|q\|_+$. The assertion is that the Weierstrass invariant $c_6$ of this curve, formed in Mathlib from the $b$-invariants by $c_6 = -b_2^3 + 36 b_2 b_4 - 216 b_6$, has norm exactly $1$: $\|($[`TateCurve.curve q`](def/TateCurve_QSeries.html#L185)$).c_6\|_+ = 1$. In particular $c_6$ is nonzero, and the statement includes the degenerate case $q = 0$, where $c_6 = -1$.
--
--   This is the standard fact that the $c_6$-invariant of the Tate curve $E_q$ over a complete non-archimedean field is a unit, the companion of the corresponding statement for $c_4$. It is used in [`WeierstrassCurve.exists_variableChange_tateCurve_algebraicClosure_galois_signBehavior`](thm.html#WeierstrassCurve.exists_variableChange_tateCurve_algebraicClosure_galois_signBehavior), where non-vanishing of $c_6$ over an algebraic closure rules out extra automorphisms of the base-changed Tate curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateCurve_nnnorm_c_six.lean

import Mathlib
import Definitions.Def_TateCurve_TateParameter

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NNReal
open scoped NNReal in

theorem TateCurve.nnnorm_c_six {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] {q : K} (hq : ‖q‖₊ < 1) :
    ‖(TateCurve.curve q).c₆‖₊ = 1 := by sorry
