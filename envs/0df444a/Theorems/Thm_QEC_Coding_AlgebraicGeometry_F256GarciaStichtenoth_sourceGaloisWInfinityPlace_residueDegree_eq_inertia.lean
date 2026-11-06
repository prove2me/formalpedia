-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWInfinityPlace_residueDegree_eq_inertia
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWInfinityPlace_residueDegree_eq_inertia
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:01:48.610227+00:00
-- url     : https://prove2.me/theorems/0a8b9a4f-889c-4a39-a7f5-e1e4a8161773
-- title:
--   F256 Garcia Stichtenoth: source Galois WInfinity Place residue Degree eq inertia
-- statement:
--   The actual residue degree at an infinity-fibre place is the common
--   inertia degree of that Galois fibre.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWResidueDegrees.lean#L387-L432
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWResidueDegrees.lean#L387-L432

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWGlobalPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneQuotientResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_InfinityResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ResidueFinrankInertia
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PlaceIncrement
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWResidueDegrees
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWResidueDegrees_wClosureAlgebra
attribute [local instance 3000] sourceGaloisWResidueDegrees_wClosureAlgebra
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWResidueDegrees_wClosureSMul
attribute [local instance 3000] sourceGaloisWResidueDegrees_wClosureSMul
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWResidueDegrees_wClosureModule
attribute [local instance 3000] sourceGaloisWResidueDegrees_wClosureModule
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWResidueDegrees_wClosureFree
attribute [local instance 3000] sourceGaloisWResidueDegrees_wClosureFree
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWResidueDegrees_wBaseFree
attribute [local instance 3000] sourceGaloisWResidueDegrees_wBaseFree
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWResidueDegrees_wClosureFaithfulSMul
attribute [local instance 3000] sourceGaloisWResidueDegrees_wClosureFaithfulSMul
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWResidueDegrees_wClosureScalarTower
attribute [local instance] sourceGaloisWResidueDegrees_wClosureScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWResidueDegrees_wClosureTorsionFree
attribute [local instance] sourceGaloisWResidueDegrees_wClosureTorsionFree
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWResidueDegrees_wClosureFiniteDimensional
attribute [local instance] sourceGaloisWResidueDegrees_wClosureFiniteDimensional
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWResidueDegrees_wClosureIsGalois
attribute [local instance] sourceGaloisWResidueDegrees_wClosureIsGalois
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWResidueDegrees_closurePolynomialAlgebra
attribute [local instance] sourceGaloisWResidueDegrees_closurePolynomialAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWResidueDegrees_closurePolynomialRatFuncScalarTower
attribute [local instance] sourceGaloisWResidueDegrees_closurePolynomialRatFuncScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWResidueDegrees_closureRatFuncIsSeparable
attribute [local instance] sourceGaloisWResidueDegrees_closureRatFuncIsSeparable
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWResidueDegrees_oBaseModule
attribute [local instance 2000] sourceGaloisWResidueDegrees_oBaseModule
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWResidueDegrees_oBaseFaithfulSMul
attribute [local instance 2000] sourceGaloisWResidueDegrees_oBaseFaithfulSMul
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWResidueDegrees_oClosureAlgebra
attribute [local instance 2000] sourceGaloisWResidueDegrees_oClosureAlgebra
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWResidueDegrees_oClosureSMul
attribute [local instance 2000] sourceGaloisWResidueDegrees_oClosureSMul
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWResidueDegrees_oClosureModule
attribute [local instance 2000] sourceGaloisWResidueDegrees_oClosureModule
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWResidueDegrees_oBaseScalarTower
attribute [local instance] sourceGaloisWResidueDegrees_oBaseScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWResidueDegrees_oIntegralClosureFractionTower
attribute [local instance] sourceGaloisWResidueDegrees_oIntegralClosureFractionTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWResidueDegrees_oIntegralClosureTorsionFree
attribute [local instance] sourceGaloisWResidueDegrees_oIntegralClosureTorsionFree
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWResidueDegrees_oIntegralClosureFinite
attribute [local instance] sourceGaloisWResidueDegrees_oIntegralClosureFinite
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWResidueDegrees_oIntegralClosureIsFractionRing
attribute [local instance] sourceGaloisWResidueDegrees_oIntegralClosureIsFractionRing
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWResidueDegrees_oIntegralClosureIsDedekind
attribute [local instance] sourceGaloisWResidueDegrees_oIntegralClosureIsDedekind
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWResidueDegrees_wRelativeGalFinite
attribute [local instance] sourceGaloisWResidueDegrees_wRelativeGalFinite
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWResidueDegrees_oIntegralClosureAction
attribute [local instance] sourceGaloisWResidueDegrees_oIntegralClosureAction
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWResidueDegrees_oIntegralClosureIsGaloisGroup
attribute [local instance] sourceGaloisWResidueDegrees_oIntegralClosureIsGaloisGroup
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWResidueDegrees_sourceGaloisWFieldConstantTower
attribute [local instance] sourceGaloisWResidueDegrees_sourceGaloisWFieldConstantTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWResidueDegrees_sourceGaloisWClosureFieldConstantTower
attribute [local instance] sourceGaloisWResidueDegrees_sourceGaloisWClosureFieldConstantTower

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWInfinityPlace_residueDegree_eq_inertia (m : ℕ)
    (P : SourceGaloisWInfinityPrime m) :
    GlobalPlace.residueDegree
        (π := sourceGaloisWResidueDegrees_closurePolynomialAlgebra m)
        (ρ := sourceGaloisClosureRatFuncAlgebra m)
        (τ := sourceGaloisWResidueDegrees_closurePolynomialRatFuncScalarTower m)
        (φ := sourceGaloisClosureFunctionField m)
        (σ := sourceGaloisWResidueDegrees_closureRatFuncIsSeparable m)
        (κ := sourceGaloisClosureConstantAlgebra m)
        (sourceGaloisWInfinityPlaceOfPrime m P) =
      sourceGaloisWInfinityInertiaDegree m := by sorry
