-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureW_integralModel_differentialGeneratorOrder
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureW_integralModel_differentialGeneratorOrder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:50:07.428907+00:00
-- url     : https://prove2.me/theorems/c9dfc3b1-ed44-496d-9a81-ead93835b494
-- title:
--   F256 Garcia Stichtenoth: source Closure W integral Model differential Generator Order
-- statement:
--   The actual intrinsic order of dz in the source normal closure is its
--   lower order times the actual index, plus the proved weak-different correction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureDifferentialOrder.lean#L67-L88
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureDifferentialOrder.lean#L67-L88

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureDifferent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_NormalizedDifferentialRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureDifferentialOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialGenerator_ne_zero

set_option autoImplicit false
open IntermediateField QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open scoped QEC.Coding.AlgebraicGeometry.AmbientPlaceModels
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
attribute [local instance] closureDifferent_modelDedekind closureDifferent_modelFinite
  closureDifferent_modelFraction closureDifferent_modelTorsionFree
variable (m : ℕ) (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A (sourceClosureWBase m)] [IsFractionRing A (sourceClosureWBase m)]
    [Algebra A (SourceGaloisClosureField m)]
    [IsScalarTower A (sourceClosureWBase m) (SourceGaloisClosureField m)]
    [Module.IsTorsionFree A (SourceGaloisClosureField m)]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureW_integralModel_differentialGeneratorOrder
    (Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A (SourceGaloisClosureField m))) :
    differentialOrder (heightOnePlace (k := F256) (K := SourceGaloisClosureField m) Q)
      (functionFieldDifferentialGenerator (k := F256) (F := SourceGaloisClosureField m))
      functionFieldDifferentialGenerator_ne_zero =
    ((Q.under A).asIdeal.ramificationIdx' Q.asIdeal : ℤ) *
      differentialOrder (heightOnePlace (k := F256) (K := sourceClosureWBase m) (Q.under A))
        (functionFieldDifferentialGenerator (k := F256) (F := sourceClosureWBase m))
        functionFieldDifferentialGenerator_ne_zero +
      2 * (((Q.under A).asIdeal.ramificationIdx' Q.asIdeal : ℤ) - 1) := by sorry
