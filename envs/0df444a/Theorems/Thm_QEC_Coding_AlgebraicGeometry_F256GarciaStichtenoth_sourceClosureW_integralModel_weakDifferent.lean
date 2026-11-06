-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureW_integralModel_weakDifferent
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureW_integralModel_weakDifferent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:47:34.732195+00:00
-- url     : https://prove2.me/theorems/2bef9941-70a4-456a-b878-5aef562e4ef0
-- title:
--   F256 Garcia Stichtenoth: source Closure W integral Model weak Different
-- statement:
--   The all-prime weak-different formula on the actual constructed normal
--   closure over its literal `k(w)` subfield. Only ordinary DVR/fraction-field
--   and inclusion structure is supplied; all chain and different facts are proved.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureDifferent.lean#L48-L63
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureDifferent.lean#L48-L63

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RefinementEndpoints
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureDifferent
set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.AmbientPlaceModels
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
variable (m : ℕ) (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A (sourceClosureWBase m)] [IsFractionRing A (sourceClosureWBase m)]
    [Algebra A (SourceGaloisClosureField m)]
    [IsScalarTower A (sourceClosureWBase m) (SourceGaloisClosureField m)]
    [Module.IsTorsionFree A (SourceGaloisClosureField m)]
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.closureDifferent_modelDedekind
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.closureDifferent_modelFinite
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.closureDifferent_modelFraction
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.closureDifferent_modelTorsionFree

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureW_integralModel_weakDifferent
    (Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A (SourceGaloisClosureField m))) :
    multiplicity Q.asIdeal (differentIdeal A (integralClosure A (SourceGaloisClosureField m))) =
      2 * ((Q.under A).asIdeal.ramificationIdx' Q.asIdeal - 1) := by sorry
