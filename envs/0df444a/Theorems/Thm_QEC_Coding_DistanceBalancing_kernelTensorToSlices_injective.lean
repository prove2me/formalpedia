-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_kernelTensorToSlices_injective
-- name    : QEC.Coding.DistanceBalancing.kernelTensorToSlices_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:22:07.637787+00:00
-- url     : https://prove2.me/theorems/6f128e8e-e6c8-4d81-9a87-3a7de891e380
-- title:
--   Distance Balancing: kernel Tensor To Slices injective
-- statement:
--   The canonical tensor-to-slices map is injective.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Dimension.lean#L305-L311
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Dimension.lean#L305-L311

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Dimension.Constructions
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Dimension
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.DistanceBalancing
universe u
open scoped TensorProduct
variable {xZero xOne xTwo classicalBit classicalCheck : Type u}
variable [Fintype xZero] [DecidableEq xZero]
variable [Fintype xOne] [DecidableEq xOne]
variable [Fintype xTwo] [DecidableEq xTwo]
variable [Fintype classicalBit] [DecidableEq classicalBit]
variable [Fintype classicalCheck] [DecidableEq classicalCheck]
variable (D : Data xZero xOne xTwo classicalBit classicalCheck)

theorem QEC.Coding.DistanceBalancing.kernelTensorToSlices_injective :
    Function.Injective (kernelTensorToSlices D) := by sorry
