-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_middleCohomologyDistanceAtLeast
-- name    : QEC.Coding.DistanceBalancing.middleCohomologyDistanceAtLeast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:19:59.254149+00:00
-- url     : https://prove2.me/theorems/915afeb4-5744-4293-866c-a87d791ad84e
-- title:
--   Distance Balancing: middle Cohomology Distance At Least
-- statement:
--   EKZ20 Theorem 2.3, cohomological-distance half: the product preserves the
--   source cohomological distance.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L784-L802
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L784-L802

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

theorem QEC.Coding.DistanceBalancing.middleCohomologyDistanceAtLeast
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (hS : IsClassicalRightInverse D S)
    {d : Nat}
    (hDistance : MiddleCohomologyDistanceAtLeast
      (sourceChainComplex D) d) :
    MiddleCohomologyDistanceAtLeast (chainComplex D) d := by sorry
