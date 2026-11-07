-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_transpose_sourceBoundary2_sourceCochainLift
-- name    : QEC.Coding.DistanceBalancing.transpose_sourceBoundary2_sourceCochainLift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:19:33.873201+00:00
-- url     : https://prove2.me/theorems/e4f256a2-1694-4b14-a02b-1c4dedf5534d
-- title:
--   Distance Balancing: transpose source Boundary2 source Cochain Lift
-- statement:
--   The lifted source cochain has exactly the required second-block
--   coboundary, by the right-inverse identity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L600-L650
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L600-L650

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

theorem QEC.Coding.DistanceBalancing.transpose_sourceBoundary2_sourceCochainLift
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (hS : IsClassicalRightInverse D S)
    (x : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hx : x ∈ (chainComplex D).middleCocycleCode.carrier)
    (b : classicalCheck) :
    wordLinearMapTranspose (sourceChainComplex D).boundary2
      (sourceCochainLift S x b) = xTwoCheckSlice x b := by sorry
