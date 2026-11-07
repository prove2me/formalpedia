-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancingSubsystem_kernelCohomologyProjection_dressedXDistanceAtLeast
-- name    : QEC.Coding.DistanceBalancingSubsystem.kernelCohomologyProjection_dressedXDistanceAtLeast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:54:32.485138+00:00
-- url     : https://prove2.me/theorems/3db57c29-56e6-4390-8097-6576c2f28a46
-- title:
--   Distance Balancing Subsystem: kernel Cohomology Projection dressed XDistance At Least
-- statement:
--   A nonzero selected kernel-contracted logical class exposes a source
--   dressed-X representative of no larger weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/SubsystemKernel.lean#L200-L242
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/SubsystemKernel.lean#L200-L242

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

theorem QEC.Coding.DistanceBalancingSubsystem.kernelCohomologyProjection_dressedXDistanceAtLeast
    {d : Nat} (hSource : SD.DressedXDistanceAtLeast d)
    (x : Word (ZMod 2)
      (DistanceBalancing.QubitIndex xOne xTwo classicalBit classicalCheck))
    (hx : x ∈ (DistanceBalancing.chainComplex
      (productData SD Y)).middleCocycleCode.carrier)
    (hLogical : kernelCohomologyProjection SD Y
      ((DistanceBalancing.chainComplex
        (productData SD Y)).middleCoboundaryInCocycles.mkQ ⟨x, hx⟩) ≠ 0) :
    d ≤ HammingWeight x := by sorry
