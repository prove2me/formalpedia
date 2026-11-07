-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256ShortenedMultiplicationCode_mem_iff
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256ShortenedMultiplicationCode_mem_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:29:26.37236+00:00
-- url     : https://prove2.me/theorems/21a003b1-4141-40d8-b4fb-dd8306c6ae93
-- title:
--   F256 Garcia Stichtenoth: f256 Shortened Multiplication Code mem iff
-- statement:
--   The concrete shortened AG code equals the source's zero-then-puncture construction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureShortening.lean#L129-L138
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureShortening.lean#L129-L138

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureEvaluation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_EvaluationShortening
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureShortening
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256ShortenedMultiplicationCode_mem_iff (i : ℕ)
    (w : Word F256 (F256MultiplicationRetained i)) :
    w ∈ (f256ShortenedMultiplicationCode i).carrier ↔
      ∃ x ∈ (f256MultiplicationCode i).carrier,
        (∀ a, x (f256MultiplicationPivot i a) = 0) ∧
        (fun j : F256MultiplicationRetained i => x j.val) = w := by sorry
