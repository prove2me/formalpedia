-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256PuncturedMultiplicationCode_dimension_eq
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256PuncturedMultiplicationCode_dimension_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:29:04.937258+00:00
-- url     : https://prove2.me/theorems/6814bd47-82fe-4819-a8aa-664259043807
-- title:
--   F256 Garcia Stichtenoth: f256 Punctured Multiplication Code dimension eq
-- statement:
--   The F256 Garcia Stichtenoth construction uses the f256 Punctured Multiplication Code dimension eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureShortening.lean#L214-L230
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureShortening.lean#L214-L230

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureEvaluation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_EvaluationShortening
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureShortening
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256PuncturedMultiplicationCode_dimension_eq (i : ℕ) :
    Dimension (f256PuncturedMultiplicationCode i) = Dimension (f256MultiplicationCode i) := by sorry
