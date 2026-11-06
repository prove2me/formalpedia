-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisClosureSelectedLength_lower_bound
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureSelectedLength_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:53:25.300394+00:00
-- url     : https://prove2.me/theorems/acd33e6a-4e71-428a-81ef-cc01126f0f24
-- title:
--   F256 Garcia Stichtenoth: source Galois Closure Selected Length lower bound
-- statement:
--   The F256 Garcia Stichtenoth construction uses the source Galois Closure Selected Length lower bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisSelectedPlaces.lean#L430-L432
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisSelectedPlaces.lean#L430-L432

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureSelectedLength_lower_bound (m : ℕ) :
    240 * 16 ^ m ≤ sourceGaloisClosureSelectedLength m := by sorry
