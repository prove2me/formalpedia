-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_sliceRemainder_mem_middleCycleCode
-- name    : QEC.Coding.DistanceBalancing.sliceRemainder_mem_middleCycleCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:20:40.08938+00:00
-- url     : https://prove2.me/theorems/cee5c764-ce6f-478c-af79-f01b023de731
-- title:
--   Distance Balancing: slice Remainder mem middle Cycle Code
-- statement:
--   The Distance Balancing construction uses the slice Remainder mem middle Cycle Code property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L1068-L1078
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L1068-L1078

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

theorem QEC.Coding.DistanceBalancing.sliceRemainder_mem_middleCycleCode
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hz : z ∈ (chainComplex D).middleCycleCode.carrier)
    (hFill : ∀ a : classicalBit,
      xOneBitSlice z a ∈ (sourceChainComplex D).middleBoundaryCode.carrier) :
    sliceRemainder D z hFill ∈ (chainComplex D).middleCycleCode.carrier := by sorry
