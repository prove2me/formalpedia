-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256MultiplicationCode_distance_lower
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256MultiplicationCode_distance_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:26:19.264407+00:00
-- url     : https://prove2.me/theorems/37164699-a028-4d21-9fa9-52172ce8f32f
-- title:
--   F256 Garcia Stichtenoth: f256 Multiplication Code distance lower
-- statement:
--   The F256 Garcia Stichtenoth construction uses the f256 Multiplication Code distance lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureEvaluation.lean#L89-L103
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureEvaluation.lean#L89-L103

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_ConstantFieldTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256MultiplicationCode_distance_lower (i : ℕ) :
    (((f256GarciaStichtenothLength i + 3) / 4 : ℕ) : WithTop ℕ) ≤
      HypergraphProduct.extendedMinimumDistance (f256MultiplicationCode i) := by sorry
