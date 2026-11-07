-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256ShortenedMultiplicationDivisor_large_degree
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256ShortenedMultiplicationDivisor_large_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:32:44.037489+00:00
-- url     : https://prove2.me/theorems/e00f7762-8b0e-4839-a333-616372016100
-- title:
--   F256 Garcia Stichtenoth: f256 Shortened Multiplication Divisor large degree
-- statement:
--   The F256 Garcia Stichtenoth construction uses the f256 Shortened Multiplication Divisor large degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureShortening.lean#L79-L86
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureShortening.lean#L79-L86

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureEvaluation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_EvaluationShortening
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureShortening
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256ShortenedMultiplicationDivisor_large_degree (i : ℕ) :
    2 * (f256GarciaStichtenothGenus i : ℤ) - 1 ≤
      Divisor.degree GlobalPlace.residueDegree (f256ShortenedMultiplicationDivisor i) := by sorry
