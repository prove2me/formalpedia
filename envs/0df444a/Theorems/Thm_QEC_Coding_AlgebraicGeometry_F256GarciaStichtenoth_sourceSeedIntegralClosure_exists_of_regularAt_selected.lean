-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSeedIntegralClosure_exists_of_regularAt_selected
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedIntegralClosure_exists_of_regularAt_selected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:32:08.561882+00:00
-- url     : https://prove2.me/theorems/5806bf1a-8931-4819-add6-7508dde11786
-- title:
--   F256 Garcia Stichtenoth: source Seed Integral Closure exists of regular At selected
-- statement:
--   A source-level function regular at every explicit place above `z = 1`
--   is represented by the integral closure of the corresponding base DVR.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSeedSplittingIdeals.lean#L524-L569
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSeedSplittingIdeals.lean#L524-L569

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedIntegralClosure_exists_of_regularAt_selected (m : ℕ)
    (x : SourceField m)
    (hx : ∀ index : SourceSelectedPlaceIndex m,
      GlobalPlace.RegularAt (sourceSelectedRationalPlace m index).place x) :
    ∃ xO : SourceSeedIntegralClosure m,
      algebraMap (SourceSeedIntegralClosure m) (SourceField m) xO = x := by sorry
