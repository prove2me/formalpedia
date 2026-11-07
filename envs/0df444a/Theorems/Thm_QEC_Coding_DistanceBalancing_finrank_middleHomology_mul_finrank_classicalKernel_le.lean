-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_finrank_middleHomology_mul_finrank_classicalKernel_le
-- name    : QEC.Coding.DistanceBalancing.finrank_middleHomology_mul_finrank_classicalKernel_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:38:50.313102+00:00
-- url     : https://prove2.me/theorems/84df10ed-bbdb-4fba-8d9b-474799cffea7
-- title:
--   Distance Balancing: finrank middle Homology mul finrank classical Kernel le
-- statement:
--   Multiplicative lower bound on the number of logical qubits in the EKZ
--   distance-balancing product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Dimension.lean#L335-L341
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Dimension.lean#L335-L341

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

theorem QEC.Coding.DistanceBalancing.finrank_middleHomology_mul_finrank_classicalKernel_le :
    Module.finrank (ZMod 2) (sourceChainComplex D).middleHomology *
        Module.finrank (ZMod 2) (ClassicalKernel D) ≤
      Module.finrank (ZMod 2) (chainComplex D).middleHomology := by sorry
