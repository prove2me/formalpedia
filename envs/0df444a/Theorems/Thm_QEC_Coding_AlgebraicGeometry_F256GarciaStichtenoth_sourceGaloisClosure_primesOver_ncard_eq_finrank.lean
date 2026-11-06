-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisClosure_primesOver_ncard_eq_finrank
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosure_primesOver_ncard_eq_finrank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:37:14.354994+00:00
-- url     : https://prove2.me/theorems/983a4116-8c9c-4744-82d3-b1f9ffe4e4ae
-- title:
--   F256 Garcia Stichtenoth: source Galois Closure primes Over ncard eq finrank
-- statement:
--   The prime fibre above the literal `z=1` place has cardinality equal to
--   the full normal-closure degree.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceNormalClosureSplitting.lean#L772-L802
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceNormalClosureSplitting.lean#L772-L802

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSeedSplittingIdeals
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceNormalClosure
import Mathlib.FieldTheory.Fixed
import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Coset.Card
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Valuation.AlgebraInstances
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceNormalClosureSplitting
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
open scoped Pointwise
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureFieldBaseAlgebraPinned
attribute [local instance 3000] sourceGaloisClosureFieldBaseAlgebraPinned
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureFieldBaseSMulPinned
attribute [local instance 3000] sourceGaloisClosureFieldBaseSMulPinned
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureFieldBaseModulePinned
attribute [local instance 3000] sourceGaloisClosureFieldBaseModulePinned
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureGalFinite
attribute [local instance 3000] sourceGaloisClosureGalFinite
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureBaseValuationRingBaseModule
attribute [local instance 2000] sourceGaloisClosureBaseValuationRingBaseModule
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureBaseValuationRingBaseFaithfulSMul
attribute [local instance 2000] sourceGaloisClosureBaseValuationRingBaseFaithfulSMul
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureSeedBaseValuationRingAlgebra
attribute [local instance 2000] sourceGaloisClosureSeedBaseValuationRingAlgebra
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureSeedBaseValuationRingSMul
attribute [local instance 2000] sourceGaloisClosureSeedBaseValuationRingSMul
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureSeedBaseValuationRingModule
attribute [local instance 2000] sourceGaloisClosureSeedBaseValuationRingModule
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureBaseValuationRingAlgebra
attribute [local instance 2000] sourceGaloisClosureBaseValuationRingAlgebra
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureBaseValuationRingSMul
attribute [local instance 2000] sourceGaloisClosureBaseValuationRingSMul
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureBaseValuationRingModule
attribute [local instance 2000] sourceGaloisClosureBaseValuationRingModule
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureBaseScalarTower
attribute [local instance] sourceGaloisClosureBaseScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureSeedBaseScalarTower
attribute [local instance] sourceGaloisClosureSeedBaseScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedIntegralClosureFractionTower
attribute [local instance] sourceSeedIntegralClosureFractionTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureIntegralClosureFractionTower
attribute [local instance] sourceGaloisClosureIntegralClosureFractionTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedIntegralClosureClosureAlgebra
attribute [local instance] sourceSeedIntegralClosureClosureAlgebra
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedIntegralClosureClosureSMul
attribute [local instance 2000] sourceSeedIntegralClosureClosureSMul
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedIntegralClosureClosureModule
attribute [local instance 2000] sourceSeedIntegralClosureClosureModule
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureIntegralClosureScalarTower
attribute [local instance] sourceGaloisClosureIntegralClosureScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureIntegralOverSeedIntegral
attribute [local instance] sourceGaloisClosureIntegralOverSeedIntegral
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureIntegralOverSeedTorsionFree
attribute [local instance] sourceGaloisClosureIntegralOverSeedTorsionFree
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureIntegralClosureTorsionFree
attribute [local instance] sourceGaloisClosureIntegralClosureTorsionFree
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureIntegralClosureFinite
attribute [local instance] sourceGaloisClosureIntegralClosureFinite
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureIntegralClosureIsFractionRing
attribute [local instance] sourceGaloisClosureIntegralClosureIsFractionRing
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureIntegralClosureIsDedekind
attribute [local instance] sourceGaloisClosureIntegralClosureIsDedekind
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureIntegralClosureAction
attribute [local instance] sourceGaloisClosureIntegralClosureAction
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureIntegralClosureSMul
attribute [local instance 3000] sourceGaloisClosureIntegralClosureSMul
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureIntegralClosureIdealAction
attribute [local instance 3000] sourceGaloisClosureIntegralClosureIdealAction
attribute [local instance 4000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureIntegralClosureIdealMulAction
attribute [local instance 4000] sourceGaloisClosureIntegralClosureIdealMulAction
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureIntegralClosureActionCommutesWithBase
attribute [local instance] sourceGaloisClosureIntegralClosureActionCommutesWithBase
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureIntegralClosureIsGaloisGroup
attribute [local instance] sourceGaloisClosureIntegralClosureIsGaloisGroup
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedClosureFieldRangeAlgebra
attribute [local instance 3000] sourceSeedClosureFieldRangeAlgebra
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedClosureFieldRangeSMul
attribute [local instance 3000] sourceSeedClosureFieldRangeSMul
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedClosureFieldRangeModule
attribute [local instance 3000] sourceSeedClosureFieldRangeModule

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosure_primesOver_ncard_eq_finrank (m : ℕ) :
    ((IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m)).ncard =
        Module.finrank GaloisBaseField (SourceGaloisClosureField m) := by sorry
