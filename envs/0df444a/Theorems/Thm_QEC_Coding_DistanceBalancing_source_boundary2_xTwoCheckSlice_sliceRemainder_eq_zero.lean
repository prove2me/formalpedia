-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_source_boundary2_xTwoCheckSlice_sliceRemainder_eq_zero
-- name    : QEC.Coding.DistanceBalancing.source_boundary2_xTwoCheckSlice_sliceRemainder_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:20:58.041517+00:00
-- url     : https://prove2.me/theorems/80a34633-08a2-4a7e-b16b-ab011365c007
-- title:
--   Distance Balancing: source boundary2 x Two Check Slice slice Remainder eq zero
-- statement:
--   After clearing the first block of a product cycle, each residual `X₂`
--   slice lies in the degree-two kernel of the source complex.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L1082-L1107
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L1082-L1107

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

theorem QEC.Coding.DistanceBalancing.source_boundary2_xTwoCheckSlice_sliceRemainder_eq_zero
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hz : z ∈ (chainComplex D).middleCycleCode.carrier)
    (hFill : ∀ a : classicalBit,
      xOneBitSlice z a ∈ (sourceChainComplex D).middleBoundaryCode.carrier)
    (b : classicalCheck) :
    (sourceChainComplex D).boundary2
      (xTwoCheckSlice (sliceRemainder D z hFill) b) = 0 := by sorry
