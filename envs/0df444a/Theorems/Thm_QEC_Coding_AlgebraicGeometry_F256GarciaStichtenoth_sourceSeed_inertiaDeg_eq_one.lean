-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSeed_inertiaDeg_eq_one
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeed_inertiaDeg_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:37:22.722592+00:00
-- url     : https://prove2.me/theorems/f1e289cd-1ed4-47d7-a410-3cd172c48671
-- title:
--   F256 Garcia Stichtenoth: source Seed inertia Deg eq one
-- statement:
--   Every prime in the completely split seed fibre has inertia degree one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSeedSplittingIdeals.lean#L655-L664
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSeedSplittingIdeals.lean#L655-L664

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSelectedBaseRestriction
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_StepPlaceTransport
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Valuation.LocalSubring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSeedSplittingIdeals
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedBaseValuationRingBaseModule
attribute [local instance 2000] sourceSeedBaseValuationRingBaseModule
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedBaseValuationRingBaseFaithfulSMul
attribute [local instance 2000] sourceSeedBaseValuationRingBaseFaithfulSMul
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedBaseValuationRingAlgebra
attribute [local instance 2000] sourceSeedBaseValuationRingAlgebra
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedBaseValuationRingSMul
attribute [local instance 2000] sourceSeedBaseValuationRingSMul
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedBaseValuationRingModule
attribute [local instance 2000] sourceSeedBaseValuationRingModule
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedBaseScalarTower
attribute [local instance] sourceSeedBaseScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedIntegralClosureTorsionFree
attribute [local instance] sourceSeedIntegralClosureTorsionFree
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedIntegralClosureFinite
attribute [local instance] sourceSeedIntegralClosureFinite
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedIntegralClosureIsFractionRing
attribute [local instance] sourceSeedIntegralClosureIsFractionRing
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedIntegralClosureIsDedekind
attribute [local instance] sourceSeedIntegralClosureIsDedekind

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeed_inertiaDeg_eq_one (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceSeedIntegralClosure m)) :
    (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).inertiaDeg'
      P.1 = 1 := by sorry
