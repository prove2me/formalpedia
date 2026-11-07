-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_middleCohomologyDistanceAtLeast_of_classical_surjective
-- name    : QEC.Coding.DistanceBalancing.middleCohomologyDistanceAtLeast_of_classical_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:22:02.507747+00:00
-- url     : https://prove2.me/theorems/e0631426-dd8f-42c5-8838-8ba98d6b6cb0
-- title:
--   Distance Balancing: middle Cohomology Distance At Least of classical surjective
-- statement:
--   Structural cohomological half: surjectivity supplies the internal right
--   inverse, and the product preserves source cohomological distance.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L1418-L1426
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L1418-L1426

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

theorem QEC.Coding.DistanceBalancing.middleCohomologyDistanceAtLeast_of_classical_surjective
    (hSurjective : Function.Surjective
      (Matrix.toLin' D.classicalBoundary))
    {d : Nat}
    (hDistance : MiddleCohomologyDistanceAtLeast
      (sourceChainComplex D) d) :
    MiddleCohomologyDistanceAtLeast (chainComplex D) d := by sorry
