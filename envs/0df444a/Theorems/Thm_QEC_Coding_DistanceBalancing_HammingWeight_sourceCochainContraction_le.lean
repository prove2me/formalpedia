-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_HammingWeight_sourceCochainContraction_le
-- name    : QEC.Coding.DistanceBalancing.HammingWeight_sourceCochainContraction_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:19:03.147978+00:00
-- url     : https://prove2.me/theorems/28c0a207-b0ae-4bf0-8f02-a7db70067099
-- title:
--   Distance Balancing: Hamming Weight source Cochain Contraction le
-- statement:
--   Contraction cannot weigh more than all first-block slices together.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L417-L427
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L417-L427

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

theorem QEC.Coding.DistanceBalancing.HammingWeight_sourceCochainContraction_le
    (x : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (c : Word (ZMod 2) classicalBit) :
    HammingWeight (sourceCochainContraction x c) ≤
      ∑ a : classicalBit, HammingWeight (xOneBitSlice x a) := by sorry
