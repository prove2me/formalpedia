-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_homologySliceMap_tensorHomologyMap_tmul
-- name    : QEC.Coding.DistanceBalancing.homologySliceMap_tensorHomologyMap_tmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:21:53.200207+00:00
-- url     : https://prove2.me/theorems/c1d892f1-edb9-4b2e-bc5e-77a3c73157a5
-- title:
--   Distance Balancing: homology Slice Map tensor Homology Map tmul
-- statement:
--   On pure tensors, homology slices are scalar multiplication by the
--   classical kernel coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Dimension.lean#L263-L283
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Dimension.lean#L263-L283

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

theorem QEC.Coding.DistanceBalancing.homologySliceMap_tensorHomologyMap_tmul
    (h : (sourceChainComplex D).middleHomology)
    (w : ClassicalKernel D) :
    homologySliceMap D (tensorHomologyMap D (h ⊗ₜ[ZMod 2] w)) =
      fun a => w.1 a • h := by sorry
