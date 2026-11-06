-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256MultiplicationDivisor_dual_distance_numerator
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256MultiplicationDivisor_dual_distance_numerator
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:41:28.822896+00:00
-- url     : https://prove2.me/theorems/2c625b0b-90d9-44a8-a5a1-59bb8e5fb440
-- title:
--   F256 Garcia Stichtenoth: f256 Multiplication Divisor dual distance numerator
-- statement:
--   The F256 Garcia Stichtenoth construction uses the f256 Multiplication Divisor dual distance numerator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureDivisor.lean#L160-L168
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureDivisor.lean#L160-L168

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ExplicitGarciaStichtenothTower
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureDivisor
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256MultiplicationDivisor_dual_distance_numerator (i : ℕ) :
    (f256GarciaStichtenothLength i : ℤ) ≤
      5 * (Divisor.degree GlobalPlace.residueDegree (f256MultiplicationDivisor i) + 2 -
        2 * (f256GarciaStichtenothGenus i : ℤ)) := by sorry
