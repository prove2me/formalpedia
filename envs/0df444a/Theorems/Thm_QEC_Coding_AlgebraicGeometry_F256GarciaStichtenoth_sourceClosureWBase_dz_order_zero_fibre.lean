-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureWBase_dz_order_zero_fibre
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureWBase_dz_order_zero_fibre
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:53:47.606197+00:00
-- url     : https://prove2.me/theorems/2d3b4027-503d-48cc-a07d-cb005f594ecc
-- title:
--   F256 Garcia Stichtenoth: source Closure WBase dz order zero fibre
-- statement:
--   The F256 Garcia Stichtenoth construction uses the source Closure WBase dz order zero fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/WBaseDifferentialOrder.lean#L115-L123
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/WBaseDifferentialOrder.lean#L115-L123

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RationalDifferentialTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWClosurePlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_WBaseDifferentialOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialGenerator_ne_zero

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureWBase_dz_order_zero_fibre (m : ℕ)
    (P : GlobalPlace F256 (sourceClosureWBase m))
    (hw : P.order (sourceGaloisWClosureGenerator m) = 1) :
    differentialOrder P (functionFieldDifferentialGenerator (k := F256) (F := sourceClosureWBase m))
      functionFieldDifferentialGenerator_ne_zero = 14 := by sorry
