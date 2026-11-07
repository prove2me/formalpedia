-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancingSubsystem_balancedKernelSubsystemData_logicalQubits
-- name    : QEC.Coding.DistanceBalancingSubsystem.balancedKernelSubsystemData_logicalQubits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:55:55.91496+00:00
-- url     : https://prove2.me/theorems/70122e8d-8cf9-4a2b-9340-b472f066aa92
-- title:
--   Distance Balancing Subsystem: balanced Kernel Subsystem Data logical Qubits
-- statement:
--   The Distance Balancing Subsystem construction uses the balanced Kernel Subsystem Data logical Qubits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/SubsystemKernel.lean#L463-L468
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/SubsystemKernel.lean#L463-L468

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_SubsystemDimension
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_SubsystemKernel
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

theorem QEC.Coding.DistanceBalancingSubsystem.balancedKernelSubsystemData_logicalQubits :
    (balancedKernelSubsystemData SD Y).logicalQubits =
      SD.logicalQubits *
        Module.finrank (ZMod 2) (ClassicalKernel (productData SD Y)) := by sorry
