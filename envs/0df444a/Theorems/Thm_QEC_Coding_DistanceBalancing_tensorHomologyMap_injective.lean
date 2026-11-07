-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_tensorHomologyMap_injective
-- name    : QEC.Coding.DistanceBalancing.tensorHomologyMap_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:22:17.412619+00:00
-- url     : https://prove2.me/theorems/bc6b6db9-8d02-4bee-9b67-11d85e6f12f1
-- title:
--   Distance Balancing: tensor Homology Map injective
-- statement:
--   The EKZ product contains the tensor product of source homology with the
--   classical kernel.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Dimension.lean#L326-L331
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Dimension.lean#L326-L331

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

theorem QEC.Coding.DistanceBalancing.tensorHomologyMap_injective :
    Function.Injective (tensorHomologyMap D) := by sorry
