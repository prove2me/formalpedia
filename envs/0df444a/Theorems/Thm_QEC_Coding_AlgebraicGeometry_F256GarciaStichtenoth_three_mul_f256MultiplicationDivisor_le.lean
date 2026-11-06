-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_three_mul_f256MultiplicationDivisor_le
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.three_mul_f256MultiplicationDivisor_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:44:10.766797+00:00
-- url     : https://prove2.me/theorems/95de88ed-3fab-4f59-b605-dfe5f5af7799
-- title:
--   F256 Garcia Stichtenoth: three mul f256 Multiplication Divisor le
-- statement:
--   The pointwise divisor inequality used in the actual residue pairing.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureDivisor.lean#L74-L89
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureDivisor.lean#L74-L89

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ExplicitGarciaStichtenothTower
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureDivisor
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.three_mul_f256MultiplicationDivisor_le (i : ℕ) :
    (3 : ℤ) • f256MultiplicationDivisor i ≤
      f256GarciaStichtenothCanonicalDivisor i + f256GarciaStichtenothDivisorD i := by sorry
