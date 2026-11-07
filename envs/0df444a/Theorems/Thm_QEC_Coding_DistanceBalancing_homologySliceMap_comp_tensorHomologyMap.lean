-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_homologySliceMap_comp_tensorHomologyMap
-- name    : QEC.Coding.DistanceBalancing.homologySliceMap_comp_tensorHomologyMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:22:13.558883+00:00
-- url     : https://prove2.me/theorems/ebea866e-30a3-46ef-897b-29de9800d965
-- title:
--   Distance Balancing: homology Slice Map comp tensor Homology Map
-- statement:
--   Slicing the constructed product-homology class gives the canonical
--   tensor-to-slices inclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Dimension.lean#L315-L322
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Dimension.lean#L315-L322

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

theorem QEC.Coding.DistanceBalancing.homologySliceMap_comp_tensorHomologyMap :
    (homologySliceMap D).comp (tensorHomologyMap D) =
      kernelTensorToSlices D := by sorry
