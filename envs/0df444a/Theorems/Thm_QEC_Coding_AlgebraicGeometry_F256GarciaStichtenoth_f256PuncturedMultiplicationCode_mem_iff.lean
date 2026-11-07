-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256PuncturedMultiplicationCode_mem_iff
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256PuncturedMultiplicationCode_mem_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:29:37.763288+00:00
-- url     : https://prove2.me/theorems/e3344ddc-f1bf-443a-81d1-2188c0bb2221
-- title:
--   F256 Garcia Stichtenoth: f256 Punctured Multiplication Code mem iff
-- statement:
--   The F256 Garcia Stichtenoth construction uses the f256 Punctured Multiplication Code mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureShortening.lean#L192-L203
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureShortening.lean#L192-L203

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureEvaluation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_EvaluationShortening
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureShortening
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256PuncturedMultiplicationCode_mem_iff (i : ℕ)
    (w : Word F256 (F256MultiplicationRetained i)) :
    w ∈ (f256PuncturedMultiplicationCode i).carrier ↔
      ∃ x ∈ (f256MultiplicationCode i).carrier,
        (fun j : F256MultiplicationRetained i => x j.val) = w := by sorry
