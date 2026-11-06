-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256MultiplicationCoefficient_upper
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256MultiplicationCoefficient_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:41:45.33493+00:00
-- url     : https://prove2.me/theorems/36f95df7-01fa-4b22-8429-122e837745af
-- title:
--   F256 Garcia Stichtenoth: f256 Multiplication Coefficient upper
-- statement:
--   The F256 Garcia Stichtenoth construction uses the f256 Multiplication Coefficient upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureDivisor.lean#L33-L36
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureDivisor.lean#L33-L36

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ExplicitGarciaStichtenothTower
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureDivisor
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256MultiplicationCoefficient_upper (i : ℕ) :
    3 * f256MultiplicationCoefficient i ≤ 16 * (f256GarciaStichtenothAlpha i : ℤ) - 2 := by sorry
