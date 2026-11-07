-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_mul_HammingWeight_classicalWordOfHomologyFunctional_le
-- name    : QEC.Coding.DistanceBalancing.mul_HammingWeight_classicalWordOfHomologyFunctional_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:21:03.873944+00:00
-- url     : https://prove2.me/theorems/77456546-82df-40f7-87f0-c4c1f67b1d97
-- title:
--   Distance Balancing: mul Hamming Weight classical Word Of Homology Functional le
-- statement:
--   Applying any homology functional gives no more total weighted support than
--   the disjoint source slices of the product word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L1268-L1291
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L1268-L1291

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

theorem QEC.Coding.DistanceBalancing.mul_HammingWeight_classicalWordOfHomologyFunctional_le
    {d : Nat}
    (hDistance : MiddleHomologyDistanceAtLeast (sourceChainComplex D) d)
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hz : z ∈ (chainComplex D).middleCycleCode.carrier)
    (φ : Module.Dual (ZMod 2) (sourceChainComplex D).middleHomology) :
    d * HammingWeight (classicalWordOfHomologyFunctional D z hz φ) ≤
      HammingWeight z := by sorry
