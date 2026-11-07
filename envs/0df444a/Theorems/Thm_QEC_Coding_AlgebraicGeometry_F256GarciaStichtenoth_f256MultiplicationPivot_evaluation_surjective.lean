-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256MultiplicationPivot_evaluation_surjective
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256MultiplicationPivot_evaluation_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:27:29.667041+00:00
-- url     : https://prove2.me/theorems/efc53699-2dab-4d10-aa41-31a1b9741326
-- title:
--   F256 Garcia Stichtenoth: f256 Multiplication Pivot evaluation surjective
-- statement:
--   The F256 Garcia Stichtenoth construction uses the f256 Multiplication Pivot evaluation surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureShortening.lean#L96-L113
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureShortening.lean#L96-L113

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureEvaluation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_EvaluationShortening
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureShortening
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256MultiplicationDivisor_selected_eq_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256MultiplicationPivot_evaluation_surjective (i : ℕ) :
    Function.Surjective (agEvaluationLinearMap (f256MultiplicationDivisor i)
      (fun a => f256GarciaStichtenothSelectedRationalPlace i (f256MultiplicationPivot i a))
      (fun a => f256MultiplicationDivisor_selected_eq_zero i (f256MultiplicationPivot i a))) := by sorry
