-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisClosureSelectedDivisor_nonnegative
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureSelectedDivisor_nonnegative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:24:13.032088+00:00
-- url     : https://prove2.me/theorems/bc0d9afa-de56-475e-8049-6c72c0a3c63c
-- title:
--   F256 Garcia Stichtenoth: source Galois Closure Selected Divisor nonnegative
-- statement:
--   The selected divisor is coefficientwise nonnegative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisSelectedDivisor.lean#L94-L96
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisSelectedDivisor.lean#L94-L96

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisSelectedPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWPrincipalDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_FinitePlaceDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisSelectedDivisor
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
open IntermediateField
open scoped BigOperators Polynomial RatFunc
noncomputable section
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisSelectedDivisor_closurePolynomialAlgebra
attribute [local instance] sourceGaloisSelectedDivisor_closurePolynomialAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisSelectedDivisor_closurePolynomialRatFuncScalarTower
attribute [local instance] sourceGaloisSelectedDivisor_closurePolynomialRatFuncScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisSelectedDivisor_closureRatFuncIsSeparable
attribute [local instance] sourceGaloisSelectedDivisor_closureRatFuncIsSeparable

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureSelectedDivisor_nonnegative (m : ℕ) :
    Divisor.Nonnegative (sourceGaloisClosureSelectedDivisor m) := by sorry
