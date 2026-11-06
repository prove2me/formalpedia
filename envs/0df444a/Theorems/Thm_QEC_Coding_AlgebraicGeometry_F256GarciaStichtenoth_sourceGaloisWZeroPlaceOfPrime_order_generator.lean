-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWZeroPlaceOfPrime_order_generator
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWZeroPlaceOfPrime_order_generator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T21:02:48.844288+00:00
-- url     : https://prove2.me/theorems/4431583b-c41d-42b4-ae42-8f66015898ef
-- title:
--   F256 Garcia Stichtenoth: source Galois WZero Place Of Prime order generator
-- statement:
--   At every zero-fibre upper place, the embedded generator has order equal
--   to the common zero ramification index.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWGlobalPlaces.lean#L465-L476
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWGlobalPlaces.lean#L465-L476

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWFibres
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWGlobalPlaces
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.wClosureAlgebra
attribute [local instance 3000] wClosureAlgebra
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.wClosureSMul
attribute [local instance 3000] wClosureSMul
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.wClosureModule
attribute [local instance 3000] wClosureModule
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.wClosureFree
attribute [local instance 3000] wClosureFree
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.wBaseFree
attribute [local instance 3000] wBaseFree
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.wClosureFaithfulSMul
attribute [local instance 3000] wClosureFaithfulSMul
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.wClosureScalarTower
attribute [local instance] wClosureScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.wClosureTorsionFree
attribute [local instance] wClosureTorsionFree
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.wClosureFiniteDimensional
attribute [local instance] wClosureFiniteDimensional
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.wClosureIsGalois
attribute [local instance] wClosureIsGalois
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.oBaseModule
attribute [local instance 2000] oBaseModule
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.oBaseFaithfulSMul
attribute [local instance 2000] oBaseFaithfulSMul
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.oClosureAlgebra
attribute [local instance 2000] oClosureAlgebra
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.oClosureSMul
attribute [local instance 2000] oClosureSMul
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.oClosureModule
attribute [local instance 2000] oClosureModule
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.oBaseScalarTower
attribute [local instance] oBaseScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.oIntegralClosureFractionTower
attribute [local instance] oIntegralClosureFractionTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.oIntegralClosureTorsionFree
attribute [local instance] oIntegralClosureTorsionFree
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.oIntegralClosureFaithfulSMul
attribute [local instance] oIntegralClosureFaithfulSMul
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.oIntegralClosureFinite
attribute [local instance] oIntegralClosureFinite
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.oIntegralClosureIsFractionRing
attribute [local instance] oIntegralClosureIsFractionRing
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.oIntegralClosureIsDedekind
attribute [local instance] oIntegralClosureIsDedekind

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWZeroPlaceOfPrime_order_generator (m : ℕ)
    (P : SourceGaloisWZeroPrime m) :
    (sourceGaloisWZeroPlaceOfPrime m P).order
        ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) :
          SourceGaloisClosureField m) =
      (sourceGaloisWZeroRamificationIndex m : ℤ) := by sorry
