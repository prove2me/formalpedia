-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisClosureSelectedVanishingFunction_principalDivisor
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureSelectedVanishingFunction_principalDivisor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:24:11.663321+00:00
-- url     : https://prove2.me/theorems/929158ad-9c52-43a6-99dd-e698c28e8248
-- title:
--   F256 Garcia Stichtenoth: source Galois Closure Selected Vanishing Function principal Divisor
-- statement:
--   The principal divisor of `w ^ 15 - 1` is its reduced selected zero fibre
--   minus its actual infinity pole fibre.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisSelectedDivisor.lean#L676-L700
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisSelectedDivisor.lean#L676-L700

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
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisSelectedDivisor_selectedDivisorBaseValuationRingBaseModule
attribute [local instance 2000] sourceGaloisSelectedDivisor_selectedDivisorBaseValuationRingBaseModule
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisSelectedDivisor_selectedDivisorBaseValuationRingBaseFaithfulSMul
attribute [local instance 2000] sourceGaloisSelectedDivisor_selectedDivisorBaseValuationRingBaseFaithfulSMul
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisSelectedDivisor_selectedDivisorBaseValuationRingAlgebra
attribute [local instance 2000] sourceGaloisSelectedDivisor_selectedDivisorBaseValuationRingAlgebra
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisSelectedDivisor_selectedDivisorBaseValuationRingSMul
attribute [local instance 2000] sourceGaloisSelectedDivisor_selectedDivisorBaseValuationRingSMul
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisSelectedDivisor_selectedDivisorBaseValuationRingModule
attribute [local instance 2000] sourceGaloisSelectedDivisor_selectedDivisorBaseValuationRingModule
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisSelectedDivisor_selectedDivisorBaseScalarTower
attribute [local instance] sourceGaloisSelectedDivisor_selectedDivisorBaseScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisSelectedDivisor_selectedDivisorIntegralClosureFractionTower
attribute [local instance] sourceGaloisSelectedDivisor_selectedDivisorIntegralClosureFractionTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisSelectedDivisor_selectedDivisorIntegralClosureTorsionFree
attribute [local instance] sourceGaloisSelectedDivisor_selectedDivisorIntegralClosureTorsionFree
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisSelectedDivisor_selectedDivisorIntegralClosureFinite
attribute [local instance] sourceGaloisSelectedDivisor_selectedDivisorIntegralClosureFinite
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisSelectedDivisor_selectedDivisorIntegralClosureIsFractionRing
attribute [local instance] sourceGaloisSelectedDivisor_selectedDivisorIntegralClosureIsFractionRing
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisSelectedDivisor_selectedDivisorIntegralClosureIsDedekind
attribute [local instance] sourceGaloisSelectedDivisor_selectedDivisorIntegralClosureIsDedekind

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureSelectedVanishingFunction_principalDivisor (m : ℕ) :
    GlobalPlace.principalDivisor (k := F256) (F := sourceGaloisSelectedDivisor_E m)
        (Units.mk0 (sourceGaloisClosureSelectedVanishingFunction m)
          (sourceGaloisClosureSelectedVanishingFunction_ne_zero m)) =
      sourceGaloisClosureSelectedDivisor m -
        (15 * sourceGaloisWInfinityRamificationIndex m) •
          sourceGaloisWInfinityFibreDivisor m := by sorry
