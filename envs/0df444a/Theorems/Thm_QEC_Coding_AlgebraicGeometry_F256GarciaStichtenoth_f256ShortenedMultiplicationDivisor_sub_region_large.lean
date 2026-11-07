-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256ShortenedMultiplicationDivisor_sub_region_large
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256ShortenedMultiplicationDivisor_sub_region_large
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:31:23.789745+00:00
-- url     : https://prove2.me/theorems/7c14081c-6fd3-4369-8f86-c297a9a87bb7
-- title:
--   F256 Garcia Stichtenoth: f256 Shortened Multiplication Divisor sub region large
-- statement:
--   Small retained regions leave the shortened divisor in the large-degree range.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureInterpolation.lean#L18-L29
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureInterpolation.lean#L18-L29

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureShortening
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureInterpolation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256ShortenedMultiplicationDivisor_sub_region_large (i : ℕ)
    (S : Finset (F256MultiplicationRetained i))
    (hS : S.card < (f256GarciaStichtenothLength i + 4) / 5 -
      f256MultiplicationLogicalCount i) :
    2 * (f256GarciaStichtenothGenus i : ℤ) - 1 ≤
      Divisor.degree GlobalPlace.residueDegree (f256ShortenedMultiplicationDivisor i) -
        Fintype.card S := by sorry
