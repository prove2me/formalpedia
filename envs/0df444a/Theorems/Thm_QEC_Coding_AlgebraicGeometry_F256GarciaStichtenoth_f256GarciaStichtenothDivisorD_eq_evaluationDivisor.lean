-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256GarciaStichtenothDivisorD_eq_evaluationDivisor
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256GarciaStichtenothDivisorD_eq_evaluationDivisor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:26:07.79061+00:00
-- url     : https://prove2.me/theorems/b0271b94-c575-40a6-921d-ad35ce80c89f
-- title:
--   F256 Garcia Stichtenoth: f256 Garcia Stichtenoth Divisor D eq evaluation Divisor
-- statement:
--   The F256 Garcia Stichtenoth construction uses the f256 Garcia Stichtenoth Divisor D eq evaluation Divisor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureEvaluation.lean#L23-L25
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureEvaluation.lean#L23-L25

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_ConstantFieldTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256GarciaStichtenothDivisorD_eq_evaluationDivisor (i : ℕ) :
    f256GarciaStichtenothDivisorD i =
      evaluationDivisor (f256GarciaStichtenothSelectedRationalPlace i) := by sorry
