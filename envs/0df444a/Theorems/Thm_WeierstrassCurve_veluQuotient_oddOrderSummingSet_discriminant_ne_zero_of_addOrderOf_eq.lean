-- Prove2me | Theorems.Thm_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq
-- name    : WeierstrassCurve.veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/c1908705-0dcc-56d2-a80d-287a00328112
-- title:
--   Nonvanishing discriminant of Vélu's odd cyclic quotient
-- statement:
--   Let $F$ be a field and let $W$ be a Weierstrass curve over $F$ which is elliptic (so its discriminant $\Delta$ is a unit). Let $n$ be a natural number and let $Q$ be a point of the associated affine curve `W.toAffine` whose additive order is exactly $2n+1$. Form the finite set $S =$ `W.oddOrderSummingSet Q n` of pairs in $F \times F$, namely the image of $\{1,\dots,n\}$ under $k \mapsto$ the coordinates of $k \bullet Q$, where the point at infinity is sent to $(0,0)$ and an affine point $(x,y)$ to $(x,y)$. Form Vélu's quotient curve `W.veluQuotient S`, which has the same $a_1, a_2, a_3$ as $W$, has $a_4$ replaced by $a_4 - 5\sum_{P \in S} \mathrm{veluT}(P)$, and has $a_6$ replaced by $a_6 - b_2\sum_{P \in S}\mathrm{veluT}(P) - 7\sum_{P \in S}\mathrm{veluW}(P)$. The assertion is that the discriminant $\Delta$ of this quotient curve is nonzero; no restriction on the characteristic of $F$ and no algebraic closedness is assumed.
--
--   This is the nonsingularity of the target of Vélu's isogeny with kernel the cyclic group $\langle Q \rangle$ of odd order, for the quotient written down from the summing set $\{Q, 2Q, \dots, nQ\}$. It discharges the nonsingularity hypotheses carried by statements about modular polynomials and quotients by lines in the level structures, and is cited by results such as [`ModularCurve.LevelP.isUnit_discriminant_quotientByLine`](thm.html#ModularCurve.LevelP.isUnit_discriminant_quotientByLine) and [`ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient_j`](thm.html#ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient_j).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

theorem WeierstrassCurve.veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq
    {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
    (n : ℕ) (Q : W.toAffine.Point) (hQ : addOrderOf Q = 2 * n + 1) :
    (W.veluQuotient (W.oddOrderSummingSet Q n)).Δ ≠ 0 := by sorry
