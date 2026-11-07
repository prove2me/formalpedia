-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_HammingWeight_inlBlock_eq_sum_xOneBitSlice
-- name    : QEC.Coding.DistanceBalancing.HammingWeight_inlBlock_eq_sum_xOneBitSlice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:20:24.240379+00:00
-- url     : https://prove2.me/theorems/c3685faf-118e-439d-88eb-a090d543c92a
-- title:
--   Distance Balancing: Hamming Weight inl Block eq sum x One Bit Slice
-- statement:
--   The first product block decomposes exactly into its disjoint
--   classical-bit slices.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L932-L940
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L932-L940

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.DistanceBalancing
universe u
open scoped BigOperators
variable {xZero xOne xTwo classicalBit classicalCheck : Type u}
variable [Fintype xZero] [DecidableEq xZero]
variable [Fintype xOne] [DecidableEq xOne]
variable [Fintype xTwo] [DecidableEq xTwo]
variable [Fintype classicalBit] [DecidableEq classicalBit]
variable [Fintype classicalCheck] [DecidableEq classicalCheck]
variable (D : Data xZero xOne xTwo classicalBit classicalCheck)

theorem QEC.Coding.DistanceBalancing.HammingWeight_inlBlock_eq_sum_xOneBitSlice
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck)) :
    HammingWeight (fun p : xOne × classicalBit => z (Sum.inl p)) =
      ∑ a : classicalBit, HammingWeight (xOneBitSlice z a) := by sorry
