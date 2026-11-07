-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancingSubsystem_balancedSubsystemData_logicalQubits
-- name    : QEC.Coding.DistanceBalancingSubsystem.balancedSubsystemData_logicalQubits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:55:25.999633+00:00
-- url     : https://prove2.me/theorems/585e64a0-73f4-4272-9e2e-cb63b38847e7
-- title:
--   Distance Balancing Subsystem: balanced Subsystem Data logical Qubits
-- statement:
--   The Distance Balancing Subsystem construction uses the balanced Subsystem Data logical Qubits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/SubsystemDimension.lean#L701-L707
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/SubsystemDimension.lean#L701-L707

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Subsystem
import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_Formula
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_SubsystemDimension
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
variable (S : Matrix classicalBit classicalCheck (ZMod 2))

theorem QEC.Coding.DistanceBalancingSubsystem.balancedSubsystemData_logicalQubits
    (hS : IsClassicalRightInverse (productData SD Y) S) :
    (balancedSubsystemData SD Y S hS).logicalQubits =
      SD.logicalQubits *
        Module.finrank (ZMod 2) (ClassicalKernel (productData SD Y)) := by sorry
