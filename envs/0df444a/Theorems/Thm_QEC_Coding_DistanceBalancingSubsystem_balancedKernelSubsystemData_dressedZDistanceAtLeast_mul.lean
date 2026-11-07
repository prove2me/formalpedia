-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancingSubsystem_balancedKernelSubsystemData_dressedZDistanceAtLeast_mul
-- name    : QEC.Coding.DistanceBalancingSubsystem.balancedKernelSubsystemData_dressedZDistanceAtLeast_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:55:52.749864+00:00
-- url     : https://prove2.me/theorems/ff75e937-a9ad-409b-8c61-675614bda937
-- title:
--   Distance Balancing Subsystem: balanced Kernel Subsystem Data dressed ZDistance At Least mul
-- statement:
--   The Distance Balancing Subsystem construction uses the balanced Kernel Subsystem Data dressed ZDistance At Least mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/SubsystemKernel.lean#L432-L454
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/SubsystemKernel.lean#L432-L454

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

theorem QEC.Coding.DistanceBalancingSubsystem.balancedKernelSubsystemData_dressedZDistanceAtLeast_mul
    {dSource dClassical : Nat}
    (hSource : SD.DressedZDistanceAtLeast dSource)
    (hClassical : ClassicalDistanceAtLeast
      (productData SD Y).classicalBoundary dClassical) :
    (balancedKernelSubsystemData SD Y).DressedZDistanceAtLeast
      (dClassical * dSource) := by sorry
