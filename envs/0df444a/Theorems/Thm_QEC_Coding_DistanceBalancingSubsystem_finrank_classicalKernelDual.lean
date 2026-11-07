-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancingSubsystem_finrank_classicalKernelDual
-- name    : QEC.Coding.DistanceBalancingSubsystem.finrank_classicalKernelDual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:55:49.592165+00:00
-- url     : https://prove2.me/theorems/7b93091a-2fce-485a-9a6a-aad1e82be7a1
-- title:
--   Distance Balancing Subsystem: finrank classical Kernel Dual
-- statement:
--   The Distance Balancing Subsystem construction uses the finrank classical Kernel Dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/SubsystemKernel.lean#L406-L409
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/SubsystemKernel.lean#L406-L409

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

theorem QEC.Coding.DistanceBalancingSubsystem.finrank_classicalKernelDual :
    Module.finrank (ZMod 2) (ClassicalKernelDual SD Y) =
      Module.finrank (ZMod 2) (ClassicalKernel (productData SD Y)) := by sorry
