-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_regularQuadraticArtinSchreier_ramificationIdx_eq_one
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.regularQuadraticArtinSchreier_ramificationIdx_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:52:08.975784+00:00
-- url     : https://prove2.me/theorems/caa186f6-8cf1-47f5-bc83-9de733a97ae4
-- title:
--   F256 Garcia Stichtenoth: regular Quadratic Artin Schreier ramification Idx eq one
-- statement:
--   Every chosen upper prime has ramification index one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RegularQuadraticStep.lean#L561-L600
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RegularQuadraticStep.lean#L561-L600

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticStepDifferent
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RegularQuadraticStep
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.regularQuadraticArtinSchreier_ramificationIdx_eq_one
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    (IsLocalRing.maximalIdeal P.valuationRing).ramificationIdx'
      (regularQuadraticArtinSchreierUpperIdeal P b hirr) = 1 := by sorry
