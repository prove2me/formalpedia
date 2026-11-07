-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_middleHomologyDistanceAtLeast_mul_of_classical_surjective
-- name    : QEC.Coding.DistanceBalancing.middleHomologyDistanceAtLeast_mul_of_classical_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:21:54.000559+00:00
-- url     : https://prove2.me/theorems/4c26ecd9-dc3b-48ac-b7c0-0eb1177a03d4
-- title:
--   Distance Balancing: middle Homology Distance At Least mul of classical surjective
-- statement:
--   Structural form of the full multiplicative distance theorem: callers
--   provide only surjectivity and the two genuine distance bounds.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L1402-L1414
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L1402-L1414

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

theorem QEC.Coding.DistanceBalancing.middleHomologyDistanceAtLeast_mul_of_classical_surjective
    (hSurjective : Function.Surjective
      (Matrix.toLin' D.classicalBoundary))
    {dSource dClassical : Nat}
    (hSource : MiddleHomologyDistanceAtLeast
      (sourceChainComplex D) dSource)
    (hClassical : ClassicalDistanceAtLeast
      D.classicalBoundary dClassical) :
    MiddleHomologyDistanceAtLeast
      (chainComplex D) (dClassical * dSource) := by sorry
