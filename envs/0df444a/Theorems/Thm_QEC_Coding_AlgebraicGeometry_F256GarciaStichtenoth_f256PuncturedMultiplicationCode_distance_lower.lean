-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256PuncturedMultiplicationCode_distance_lower
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256PuncturedMultiplicationCode_distance_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:29:45.123593+00:00
-- url     : https://prove2.me/theorems/a090b31d-23d1-4f5d-9db4-a18824f0ba69
-- title:
--   F256 Garcia Stichtenoth: f256 Punctured Multiplication Code distance lower
-- statement:
--   The F256 Garcia Stichtenoth construction uses the f256 Punctured Multiplication Code distance lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureShortening.lean#L232-L247
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureShortening.lean#L232-L247

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureEvaluation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_EvaluationShortening
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureShortening
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256PuncturedMultiplicationCode_distance_lower (i : ℕ) :
    (((f256GarciaStichtenothLength i + 3) / 4 - f256MultiplicationLogicalCount i : ℕ) : WithTop ℕ) ≤
      HypergraphProduct.extendedMinimumDistance (f256PuncturedMultiplicationCode i) := by sorry
