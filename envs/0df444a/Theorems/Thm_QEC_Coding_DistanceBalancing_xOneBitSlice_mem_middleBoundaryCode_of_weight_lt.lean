-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_xOneBitSlice_mem_middleBoundaryCode_of_weight_lt
-- name    : QEC.Coding.DistanceBalancing.xOneBitSlice_mem_middleBoundaryCode_of_weight_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:20:24.566203+00:00
-- url     : https://prove2.me/theorems/a25adffd-5066-464f-a7c6-76b67542484e
-- title:
--   Distance Balancing: x One Bit Slice mem middle Boundary Code of weight lt
-- statement:
--   Below the source homology distance, every `X₁` slice of a product cycle is
--   already a source boundary.  The remaining EKZ argument uses surjectivity of the
--   classical boundary to choose these fillings compatibly.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L988-L1001
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L988-L1001

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

theorem QEC.Coding.DistanceBalancing.xOneBitSlice_mem_middleBoundaryCode_of_weight_lt
    {d : Nat}
    (hDistance : MiddleHomologyDistanceAtLeast (sourceChainComplex D) d)
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hz : z ∈ (chainComplex D).middleCycleCode.carrier)
    (hWeight : HammingWeight z < d)
    (a : classicalBit) :
    xOneBitSlice z a ∈ (sourceChainComplex D).middleBoundaryCode.carrier := by sorry
