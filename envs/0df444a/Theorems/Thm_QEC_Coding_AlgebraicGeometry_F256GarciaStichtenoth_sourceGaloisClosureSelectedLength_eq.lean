-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisClosureSelectedLength_eq
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureSelectedLength_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:54:39.188713+00:00
-- url     : https://prove2.me/theorems/379fe2bf-5560-453a-90c6-98295bc334ce
-- title:
--   F256 Garcia Stichtenoth: source Galois Closure Selected Length eq
-- statement:
--   The F256 Garcia Stichtenoth construction uses the source Galois Closure Selected Length eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisSelectedPlaces.lean#L371-L374
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisSelectedPlaces.lean#L371-L374

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisFunctionField
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceNormalClosureSplitting
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisSelectedPlaces
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.galoisSelectedBaseValuationRingBaseModule
attribute [local instance 2000] galoisSelectedBaseValuationRingBaseModule
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.galoisSelectedBaseValuationRingBaseFaithfulSMul
attribute [local instance 2000] galoisSelectedBaseValuationRingBaseFaithfulSMul
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.galoisSelectedBaseValuationRingAlgebra
attribute [local instance 2000] galoisSelectedBaseValuationRingAlgebra
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.galoisSelectedBaseValuationRingSMul
attribute [local instance 2000] galoisSelectedBaseValuationRingSMul
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.galoisSelectedBaseValuationRingModule
attribute [local instance 2000] galoisSelectedBaseValuationRingModule
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.galoisSelectedBaseScalarTower
attribute [local instance] galoisSelectedBaseScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.galoisSelectedIntegralClosureFractionTower
attribute [local instance] galoisSelectedIntegralClosureFractionTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.galoisSelectedIntegralClosureTorsionFree
attribute [local instance] galoisSelectedIntegralClosureTorsionFree
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.galoisSelectedIntegralClosureFinite
attribute [local instance] galoisSelectedIntegralClosureFinite
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.galoisSelectedIntegralClosureIsFractionRing
attribute [local instance] galoisSelectedIntegralClosureIsFractionRing
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.galoisSelectedIntegralClosureIsDedekind
attribute [local instance] galoisSelectedIntegralClosureIsDedekind

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureSelectedLength_eq (m : ℕ) :
    sourceGaloisClosureSelectedLength m =
      Module.finrank GaloisBaseField (SourceGaloisClosureField m) := by sorry
