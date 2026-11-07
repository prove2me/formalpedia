-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256ShortenedMultiplicationDivisor_degree
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256ShortenedMultiplicationDivisor_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:26:39.163686+00:00
-- url     : https://prove2.me/theorems/f7492980-c478-4e93-af67-0ac921eac9cc
-- title:
--   F256 Garcia Stichtenoth: f256 Shortened Multiplication Divisor degree
-- statement:
--   The F256 Garcia Stichtenoth construction uses the f256 Shortened Multiplication Divisor degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureShortening.lean#L72-L77
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureShortening.lean#L72-L77

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureEvaluation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_EvaluationShortening
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureShortening
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256ShortenedMultiplicationDivisor_degree (i : ℕ) :
    Divisor.degree GlobalPlace.residueDegree (f256ShortenedMultiplicationDivisor i) =
      Divisor.degree GlobalPlace.residueDegree (f256MultiplicationDivisor i) -
        f256MultiplicationLogicalCount i := by sorry
