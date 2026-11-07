-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancingSubsystem_productDressedZDistanceAtLeast_mul
-- name    : QEC.Coding.DistanceBalancingSubsystem.productDressedZDistanceAtLeast_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:34:36.646605+00:00
-- url     : https://prove2.me/theorems/c2e8347d-d0f0-4954-9ec9-0475d7737020
-- title:
--   Distance Balancing Subsystem: product Dressed ZDistance At Least mul
-- statement:
--   EKZ homological distance multiplication for the selected subsystem
--   sector.  This is the dressed analogue of
--   `DistanceBalancing.middleHomologyDistanceAtLeast_mul`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Subsystem.lean#L317-L344
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Subsystem.lean#L317-L344

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

theorem QEC.Coding.DistanceBalancingSubsystem.productDressedZDistanceAtLeast_mul
    {dSource dClassical : Nat}
    (hSource : SD.DressedZDistanceAtLeast dSource)
    (hClassical : ClassicalDistanceAtLeast
      (productData SD Y).classicalBoundary dClassical) :
    ProductDressedZDistanceAtLeast SD Y (dClassical * dSource) := by sorry
