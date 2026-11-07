-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256MultiplicationCode_dimension_lower
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256MultiplicationCode_dimension_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:25:09.446082+00:00
-- url     : https://prove2.me/theorems/6759d437-2734-4854-a5a8-32a1240bc61e
-- title:
--   F256 Garcia Stichtenoth: f256 Multiplication Code dimension lower
-- statement:
--   The F256 Garcia Stichtenoth construction uses the f256 Multiplication Code dimension lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureEvaluation.lean#L83-L87
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureEvaluation.lean#L83-L87

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_ConstantFieldTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256MultiplicationCode_dimension_lower (i : ℕ) :
    f256GarciaStichtenothLength i ≤ 4 * Dimension (f256MultiplicationCode i) := by sorry
