-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_source_boundary2_xTwoBitFilling
-- name    : QEC.Coding.DistanceBalancing.source_boundary2_xTwoBitFilling
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:20:48.090112+00:00
-- url     : https://prove2.me/theorems/c5da2d73-66fc-44c4-83d7-3b0e2933237c
-- title:
--   Distance Balancing: source boundary2 x Two Bit Filling
-- statement:
--   The Distance Balancing construction uses the source boundary2 x Two Bit Filling property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L1013-L1023
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L1013-L1023

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

theorem QEC.Coding.DistanceBalancing.source_boundary2_xTwoBitFilling
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hFill : ∀ a : classicalBit,
      xOneBitSlice z a ∈ (sourceChainComplex D).middleBoundaryCode.carrier)
    (a : classicalBit) :
    (sourceChainComplex D).boundary2 (xTwoBitFilling D z hFill a) =
      xOneBitSlice z a := by sorry
