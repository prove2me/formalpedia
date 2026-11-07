-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancingSubsystem_selectedHomologySliceMap_comp_tensorHomologyMap
-- name    : QEC.Coding.DistanceBalancingSubsystem.selectedHomologySliceMap_comp_tensorHomologyMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:33:41.110449+00:00
-- url     : https://prove2.me/theorems/af77c01a-6a9a-43b3-9545-ed307fed074e
-- title:
--   Distance Balancing Subsystem: selected Homology Slice Map comp tensor Homology Map
-- statement:
--   The Distance Balancing Subsystem construction uses the selected Homology Slice Map comp tensor Homology Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Subsystem.lean#L169-L185
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Subsystem.lean#L169-L185

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Dimension
import Definitions.Def_QEC_Coding_ChainComplex_Homotopy
import Definitions.Def_QEC_Coding_CSS_Subsystem
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Subsystem
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.DistanceBalancingSubsystem
open QEC.Coding
open QEC.Coding.DistanceBalancing
open scoped TensorProduct
universe u v
variable {xZero xOne xTwo classicalBit classicalCheck : Type u}
variable [Fintype xZero] [DecidableEq xZero]
variable [Fintype xOne] [DecidableEq xOne]
variable [Fintype xTwo] [DecidableEq xTwo]
variable [Fintype classicalBit] [DecidableEq classicalBit]
variable [Nonempty classicalBit]
variable [Fintype classicalCheck] [DecidableEq classicalCheck]
variable {LogicalZ LogicalX : Type v}
variable [AddCommGroup LogicalZ] [Module (ZMod 2) LogicalZ]
variable [AddCommGroup LogicalX] [Module (ZMod 2) LogicalX]
variable [Module.Finite (ZMod 2) LogicalZ]
variable [Module.Finite (ZMod 2) LogicalX]
variable (SD : SubsystemCSSData xZero xOne xTwo LogicalZ LogicalX)
variable (Y : Word (ZMod 2) classicalBit →ₗ[ZMod 2]
  Word (ZMod 2) classicalCheck)

theorem QEC.Coding.DistanceBalancingSubsystem.selectedHomologySliceMap_comp_tensorHomologyMap :
    (selectedHomologySliceMap SD Y).comp
        (tensorHomologyMap (productData SD Y)) =
      (kernelTensorToZLogicalSlices SD Y).comp
        (sourceLogicalTensorProjection SD Y) := by sorry
