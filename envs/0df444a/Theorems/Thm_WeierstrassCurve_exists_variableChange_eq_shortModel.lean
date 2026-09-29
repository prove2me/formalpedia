-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_variableChange_eq_shortModel
-- name    : WeierstrassCurve.exists_variableChange_eq_shortModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/58c8e531-da41-5076-9756-784d96cd269b
-- title:
--   Characteristic-zero Weierstrass curves admit the model y²=x³-27c₄x-54c₆
-- statement:
--   Let $K$ be a field of characteristic zero and let $W$ be a Weierstrass curve over $K$, i.e. a tuple of coefficients $(a_1,a_2,a_3,a_4,a_6)$ in $K$ presenting $y^2+a_1xy+a_3y=x^3+a_2x^2+a_4x+a_6$, with its usual invariants $c_4$ and $c_6$ built from $b_2=a_1^2+4a_2$, $b_4=2a_4+a_1a_3$, $b_6=a_3^2+4a_6$ by $c_4=b_2^2-24b_4$ and $c_6=-b_2^3+36b_2b_4-216b_6$. The assertion is that there exists an admissible change of variables $C$ over $K$ — an element of `WeierstrassCurve.VariableChange K`, given by a unit $u$ of $K$ together with $r,s,t \in K$ — whose action on $W$ yields exactly the Weierstrass curve with coefficients $a_1=a_2=a_3=0$, $a_4=-27\,W.c_4$ and $a_6=-54\,W.c_6$, that is the short model $y^2=x^3-27c_4x-54c_6$. Equality here is equality of coefficient tuples, and no nonsingularity (nonvanishing of the discriminant) hypothesis is imposed on $W$.
--
--   This is the classical normalisation of a Weierstrass equation in characteristic zero: completing the square and the cube and then rescaling by $u=1/6$ turns the invariants $c_4,c_6$ themselves into the coefficients of the model $y^2=x^3-27c_4x-54c_6$. It is used in the construction of the auxiliary curve with prescribed $c_4$ and $c_6$ entering the $3$–$5$ switch, being cited by [`WeierstrassCurve.threeFiveAuxiliaryCurveExists`](thm.html#WeierstrassCurve.threeFiveAuxiliaryCurveExists).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_variableChange_eq_shortModel.lean

import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.Data.Int.ModEq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.exists_variableChange_eq_shortModel {K : Type*} [Field K] [CharZero K] (W : WeierstrassCurve K) : ∃ C : WeierstrassCurve.VariableChange K, C • W = ⟨0, 0, 0, -27 * W.c₄, -54 * W.c₆⟩ := by sorry
