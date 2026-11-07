-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancingSubsystem_productDressedXDistanceAtLeast
-- name    : QEC.Coding.DistanceBalancingSubsystem.productDressedXDistanceAtLeast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:34:08.072364+00:00
-- url     : https://prove2.me/theorems/c4a44113-97b7-41c2-a0af-b7ca05272cc2
-- title:
--   Distance Balancing Subsystem: product Dressed XDistance At Least
-- statement:
--   EKZ cohomological distance preservation for the selected subsystem
--   sector.  A nonzero projected product class exposes an actual nonzero selected
--   source cohomology slice, to which the source dressed bound applies.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Subsystem.lean#L349-L389
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Subsystem.lean#L349-L389

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

theorem QEC.Coding.DistanceBalancingSubsystem.productDressedXDistanceAtLeast
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (hS : IsClassicalRightInverse (productData SD Y) S)
    {d : Nat}
    (hSource : SD.DressedXDistanceAtLeast d) :
    ProductDressedXDistanceAtLeast SD Y S hS d := by sorry
