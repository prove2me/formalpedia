-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256MultiplicationDivisor_degree_upper
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256MultiplicationDivisor_degree_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:41:08.987886+00:00
-- url     : https://prove2.me/theorems/6e41fc8a-bb0d-4395-a854-e942a64bc9cc
-- title:
--   F256 Garcia Stichtenoth: f256 Multiplication Divisor degree upper
-- statement:
--   The F256 Garcia Stichtenoth construction uses the f256 Multiplication Divisor degree upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureDivisor.lean#L133-L141
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureDivisor.lean#L133-L141

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ExplicitGarciaStichtenothTower
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureDivisor
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256MultiplicationDivisor_degree_upper (i : ℕ) :
    45 * Divisor.degree GlobalPlace.residueDegree (f256MultiplicationDivisor i) ≤
      16 * (f256GarciaStichtenothLength i : ℤ) := by sorry
