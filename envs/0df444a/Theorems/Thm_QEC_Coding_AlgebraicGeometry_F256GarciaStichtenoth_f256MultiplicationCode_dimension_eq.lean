-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256MultiplicationCode_dimension_eq
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256MultiplicationCode_dimension_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:24:18.156205+00:00
-- url     : https://prove2.me/theorems/bd49bff4-20ee-457a-b57a-279fce2bcdee
-- title:
--   F256 Garcia Stichtenoth: f256 Multiplication Code dimension eq
-- statement:
--   The F256 Garcia Stichtenoth construction uses the f256 Multiplication Code dimension eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureEvaluation.lean#L66-L81
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureEvaluation.lean#L66-L81

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_ConstantFieldTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256MultiplicationCode_dimension_eq (i : ℕ) :
    (Dimension (f256MultiplicationCode i) : ℤ) =
      Divisor.degree GlobalPlace.residueDegree (f256MultiplicationDivisor i) + 1 -
        f256GarciaStichtenothGenus i := by sorry
