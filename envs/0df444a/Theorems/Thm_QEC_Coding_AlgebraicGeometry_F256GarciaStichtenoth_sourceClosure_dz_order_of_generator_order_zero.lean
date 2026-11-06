-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosure_dz_order_of_generator_order_zero
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosure_dz_order_of_generator_order_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:22:25.683258+00:00
-- url     : https://prove2.me/theorems/4e4e2c52-9ee2-4957-8ac1-4b5ca277611a
-- title:
--   F256 Garcia Stichtenoth: source Closure dz order of generator order zero
-- statement:
--   The actual source normal closure has dz-order zero at every supplied
--   global place with unit w; the model centre does not change that place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureRegularDifferentialOrder.lean#L61-L76
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureRegularDifferentialOrder.lean#L61-L76

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureUnramified
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_WBaseDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialPlaceTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureRegularDifferentialOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialGenerator_ne_zero

set_option autoImplicit false
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosure_dz_order_of_generator_order_zero
    (Q : GlobalPlace F256 (SourceGaloisClosureField m))
    (hw : Q.order (sourceGaloisWClosureGenerator m : SourceGaloisClosureField m) = 0) :
    differentialOrder Q
      (functionFieldDifferentialGenerator (k := F256) (F := SourceGaloisClosureField m))
      functionFieldDifferentialGenerator_ne_zero = 0 := by sorry
