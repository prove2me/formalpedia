-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancingSubsystem_kernelTensorZLogicalRetraction_apply
-- name    : QEC.Coding.DistanceBalancingSubsystem.kernelTensorZLogicalRetraction_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:33:27.995197+00:00
-- url     : https://prove2.me/theorems/e3efffb4-f962-4e11-8854-dfcdb7c97afe
-- title:
--   Distance Balancing Subsystem: kernel Tensor ZLogical Retraction apply
-- statement:
--   The Distance Balancing Subsystem construction uses the kernel Tensor ZLogical Retraction apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Subsystem.lean#L161-L167
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Subsystem.lean#L161-L167

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

theorem QEC.Coding.DistanceBalancingSubsystem.kernelTensorZLogicalRetraction_apply
    (t : LogicalZ ⊗[ZMod 2] ClassicalKernel (productData SD Y)) :
    kernelTensorZLogicalRetraction SD Y
        (kernelTensorToZLogicalSlices SD Y t) = t := by sorry
