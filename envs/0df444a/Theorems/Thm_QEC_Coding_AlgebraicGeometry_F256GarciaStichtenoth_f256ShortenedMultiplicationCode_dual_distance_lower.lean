-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256ShortenedMultiplicationCode_dual_distance_lower
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256ShortenedMultiplicationCode_dual_distance_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:28:56.316524+00:00
-- url     : https://prove2.me/theorems/4b7abbfe-bfe6-4afb-b27c-18df25093414
-- title:
--   F256 Garcia Stichtenoth: f256 Shortened Multiplication Code dual distance lower
-- statement:
--   The F256 Garcia Stichtenoth construction uses the f256 Shortened Multiplication Code dual distance lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureShortening.lean#L161-L184
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureShortening.lean#L161-L184

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureEvaluation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_EvaluationShortening
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureShortening
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256ShortenedMultiplicationCode_dual_distance_lower (i : ℕ) :
    (((f256GarciaStichtenothLength i + 4) / 5 - f256MultiplicationLogicalCount i : ℕ) : WithTop ℕ) ≤
      HypergraphProduct.extendedMinimumDistance (f256ShortenedMultiplicationCode i).dual := by sorry
