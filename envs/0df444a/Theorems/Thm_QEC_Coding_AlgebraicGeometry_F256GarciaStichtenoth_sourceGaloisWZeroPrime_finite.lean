-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWZeroPrime_finite
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWZeroPrime_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:58:59.863208+00:00
-- url     : https://prove2.me/theorems/86393728-09ad-4044-842e-da762408fbbb
-- title:
--   F256 Garcia Stichtenoth: source Galois WZero Prime finite
-- statement:
--   The genuine zero-place upper-prime fibre is finite.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWFibres.lean#L320-L325
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWFibres.lean#L320-L325

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisSelectedPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWClosurePlaces
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Valuation.AlgebraInstances
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWFibres
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWPlaceValuationRingBaseModule
attribute [local instance 2000] sourceGaloisWPlaceValuationRingBaseModule
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWPlaceValuationRingBaseFaithfulSMul
attribute [local instance 2000] sourceGaloisWPlaceValuationRingBaseFaithfulSMul
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWClosureFieldClosureAlgebra
attribute [local instance 3000] sourceGaloisWClosureFieldClosureAlgebra
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWClosureFieldClosureSMul
attribute [local instance 3000] sourceGaloisWClosureFieldClosureSMul
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWClosureFieldClosureModule
attribute [local instance 3000] sourceGaloisWClosureFieldClosureModule
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWClosureFieldClosureFree
attribute [local instance 3000] sourceGaloisWClosureFieldClosureFree
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWClosureFieldBaseFree
attribute [local instance 3000] sourceGaloisWClosureFieldBaseFree
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWClosureFieldClosureFaithfulSMul
attribute [local instance 3000] sourceGaloisWClosureFieldClosureFaithfulSMul
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWClosureFieldClosureScalarTower
attribute [local instance] sourceGaloisWClosureFieldClosureScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWClosureFieldClosureTorsionFree
attribute [local instance] sourceGaloisWClosureFieldClosureTorsionFree
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWClosureFieldClosureFiniteDimensional
attribute [local instance] sourceGaloisWClosureFieldClosureFiniteDimensional
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWClosureFieldClosureIsGalois
attribute [local instance] sourceGaloisWClosureFieldClosureIsGalois
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWPlaceValuationRingClosureAlgebra
attribute [local instance 2000] sourceGaloisWPlaceValuationRingClosureAlgebra
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWPlaceValuationRingClosureSMul
attribute [local instance 2000] sourceGaloisWPlaceValuationRingClosureSMul
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWPlaceValuationRingClosureModule
attribute [local instance 2000] sourceGaloisWPlaceValuationRingClosureModule
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWPlaceBaseScalarTower
attribute [local instance] sourceGaloisWPlaceBaseScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWPlaceIntegralClosureFractionTower
attribute [local instance] sourceGaloisWPlaceIntegralClosureFractionTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWRelativeGalFinite
attribute [local instance] sourceGaloisWRelativeGalFinite
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWPlaceIntegralClosureTorsionFree
attribute [local instance] sourceGaloisWPlaceIntegralClosureTorsionFree
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWPlaceIntegralClosureFaithfulSMul
attribute [local instance] sourceGaloisWPlaceIntegralClosureFaithfulSMul
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWPlaceIntegralClosureFinite
attribute [local instance] sourceGaloisWPlaceIntegralClosureFinite
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWPlaceIntegralClosureIsFractionRing
attribute [local instance] sourceGaloisWPlaceIntegralClosureIsFractionRing
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWPlaceIntegralClosureIsDedekind
attribute [local instance] sourceGaloisWPlaceIntegralClosureIsDedekind
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWPlaceIntegralClosureAction
attribute [local instance] sourceGaloisWPlaceIntegralClosureAction
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWPlaceIntegralClosureIsGaloisGroup
attribute [local instance] sourceGaloisWPlaceIntegralClosureIsGaloisGroup

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWZeroPrime_finite (m : ℕ) :
    Set.Finite (SourceGaloisWZeroPrime m) := by sorry
