-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256MultiplicationDivisor_degree
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256MultiplicationDivisor_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:42:33.517959+00:00
-- url     : https://prove2.me/theorems/80d8a767-8133-4df4-b16a-5eece3fca3bb
-- title:
--   F256 Garcia Stichtenoth: f256 Multiplication Divisor degree
-- statement:
--   The F256 Garcia Stichtenoth construction uses the f256 Multiplication Divisor degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureDivisor.lean#L91-L98
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureDivisor.lean#L91-L98

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ExplicitGarciaStichtenothTower
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureDivisor
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256MultiplicationDivisor_degree (i : ℕ) :
    Divisor.degree GlobalPlace.residueDegree (f256MultiplicationDivisor i) =
      f256MultiplicationCoefficient i *
        Divisor.degree GlobalPlace.residueDegree (f256GarciaStichtenothDivisorA i) := by sorry
