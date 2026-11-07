-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancingSubsystem_productHomologyProjection_tensorHomologyMap
-- name    : QEC.Coding.DistanceBalancingSubsystem.productHomologyProjection_tensorHomologyMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:33:50.802854+00:00
-- url     : https://prove2.me/theorems/8781dfb4-b2cb-4c02-a928-095bc14646ab
-- title:
--   Distance Balancing Subsystem: product Homology Projection tensor Homology Map
-- statement:
--   The Distance Balancing Subsystem construction uses the product Homology Projection tensor Homology Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Subsystem.lean#L195-L205
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Subsystem.lean#L195-L205

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

theorem QEC.Coding.DistanceBalancingSubsystem.productHomologyProjection_tensorHomologyMap
    (t : (sourceChainComplex (productData SD Y)).middleHomology ⊗[ZMod 2]
      ClassicalKernel (productData SD Y)) :
    productHomologyProjection SD Y
        (tensorHomologyMap (productData SD Y) t) =
      sourceLogicalTensorProjection SD Y t := by sorry
