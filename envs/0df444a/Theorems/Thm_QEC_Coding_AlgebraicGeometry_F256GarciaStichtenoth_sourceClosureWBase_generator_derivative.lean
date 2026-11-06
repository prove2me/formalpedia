-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureWBase_generator_derivative
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureWBase_generator_derivative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:52:49.775205+00:00
-- url     : https://prove2.me/theorems/812dd75d-3702-4bf3-9400-9761fb30e7f7
-- title:
--   F256 Garcia Stichtenoth: source Closure WBase generator derivative
-- statement:
--   Differentiating the literal source relation computes dw/dz.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/WBaseDifferentialOrder.lean#L83-L102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/WBaseDifferentialOrder.lean#L83-L102

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RationalDifferentialTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWClosurePlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_WBaseDifferentialOrder
set_option autoImplicit false
open IntermediateField QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 5000] Algebra.toSMul Algebra.toModule
attribute [local instance] wConstantBaseTower
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.wBaseField
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.wBaseOriginalBaseAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.wBaseOriginalRationalAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.wBaseOriginalConstantAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.wBaseCharacteristic
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.wBaseConstantTower

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureWBase_generator_derivative (m : ℕ) :
    functionFieldDerivation (k := F256) (F := sourceClosureWBase m)
      (sourceGaloisWClosureGenerator m) =
        (sourceGaloisWClosureGenerator m : sourceClosureWBase m)⁻¹ ^ 14 := by sorry
