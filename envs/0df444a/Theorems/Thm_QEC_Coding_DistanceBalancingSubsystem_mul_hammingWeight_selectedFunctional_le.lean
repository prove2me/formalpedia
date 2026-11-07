-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancingSubsystem_mul_hammingWeight_selectedFunctional_le
-- name    : QEC.Coding.DistanceBalancingSubsystem.mul_hammingWeight_selectedFunctional_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:33:51.136201+00:00
-- url     : https://prove2.me/theorems/e123befb-818a-451d-b98d-10156684a5b8
-- title:
--   Distance Balancing Subsystem: mul hamming Weight selected Functional le
-- statement:
--   The source dressed-Z bound controls the weighted support of every scalar
--   functional applied after the selected logical projection.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Subsystem.lean#L278-L312
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Subsystem.lean#L278-L312

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

theorem QEC.Coding.DistanceBalancingSubsystem.mul_hammingWeight_selectedFunctional_le
    {d : Nat}
    (hSource : SD.DressedZDistanceAtLeast d)
    (z : Word (ZMod 2)
      (DistanceBalancing.QubitIndex xOne xTwo classicalBit classicalCheck))
    (hz : z ∈ (DistanceBalancing.chainComplex
      (productData SD Y)).middleCycleCode.carrier)
    (phi : Module.Dual (ZMod 2) LogicalZ) :
    d * HammingWeight
        (classicalWordOfHomologyFunctional (productData SD Y) z hz
          (phi.comp (sourceHomologyProjection SD Y))) ≤
      HammingWeight z := by sorry
