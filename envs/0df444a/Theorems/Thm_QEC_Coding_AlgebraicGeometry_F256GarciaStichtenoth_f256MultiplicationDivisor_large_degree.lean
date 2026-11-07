-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256MultiplicationDivisor_large_degree
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256MultiplicationDivisor_large_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:45:32.270206+00:00
-- url     : https://prove2.me/theorems/5d06f684-a212-4ab9-9341-5b01601d7869
-- title:
--   F256 Garcia Stichtenoth: f256 Multiplication Divisor large degree
-- statement:
--   The F256 Garcia Stichtenoth construction uses the f256 Multiplication Divisor large degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureDivisor.lean#L170-L175
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureDivisor.lean#L170-L175

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ExplicitGarciaStichtenothTower
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureDivisor
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256MultiplicationDivisor_large_degree (i : ℕ) :
    2 * (f256GarciaStichtenothGenus i : ℤ) - 1 ≤
      Divisor.degree GlobalPlace.residueDegree (f256MultiplicationDivisor i) := by sorry
