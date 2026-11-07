-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_middleHomologyDistanceAtLeast
-- name    : QEC.Coding.DistanceBalancing.middleHomologyDistanceAtLeast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:21:15.943446+00:00
-- url     : https://prove2.me/theorems/2e0518d5-55e5-44d5-9a91-c5e4d214d026
-- title:
--   Distance Balancing: middle Homology Distance At Least
-- statement:
--   EKZ20 Theorem 2.3, homological-distance half: a classical right inverse
--   preserves the source middle-homology distance.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L1249-L1264
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L1249-L1264

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

theorem QEC.Coding.DistanceBalancing.middleHomologyDistanceAtLeast
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (hS : IsClassicalRightInverse D S)
    {d : Nat}
    (hDistance : MiddleHomologyDistanceAtLeast (sourceChainComplex D) d) :
    MiddleHomologyDistanceAtLeast (chainComplex D) d := by sorry
