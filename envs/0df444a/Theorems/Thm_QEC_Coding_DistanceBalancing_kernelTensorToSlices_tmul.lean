-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_kernelTensorToSlices_tmul
-- name    : QEC.Coding.DistanceBalancing.kernelTensorToSlices_tmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:21:43.294341+00:00
-- url     : https://prove2.me/theorems/ca5eadf3-cf1e-4ef1-8a7b-bcd6fa4a0460
-- title:
--   Distance Balancing: kernel Tensor To Slices tmul
-- statement:
--   The Distance Balancing construction uses the kernel Tensor To Slices tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Dimension.lean#L296-L302
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Dimension.lean#L296-L302

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

theorem QEC.Coding.DistanceBalancing.kernelTensorToSlices_tmul
    (h : (sourceChainComplex D).middleHomology)
    (w : ClassicalKernel D) :
    kernelTensorToSlices D (h ⊗ₜ[ZMod 2] w) = fun a ↦ w.1 a • h := by sorry
