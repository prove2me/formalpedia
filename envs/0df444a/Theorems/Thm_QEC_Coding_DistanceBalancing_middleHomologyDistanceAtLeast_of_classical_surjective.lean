-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_middleHomologyDistanceAtLeast_of_classical_surjective
-- name    : QEC.Coding.DistanceBalancing.middleHomologyDistanceAtLeast_of_classical_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:37:57.4681+00:00
-- url     : https://prove2.me/theorems/b593e617-89db-4001-a3d0-7fe1e36d3bb3
-- title:
--   Distance Balancing: middle Homology Distance At Least of classical surjective
-- statement:
--   EKZ20 Theorem 2.3, homological-distance half in its structural form:
--   surjectivity of the classical boundary is enough to preserve the source
--   middle-homology distance.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L1391-L1398
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L1391-L1398

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

theorem QEC.Coding.DistanceBalancing.middleHomologyDistanceAtLeast_of_classical_surjective
    (hSurjective : Function.Surjective
      (Matrix.toLin' D.classicalBoundary))
    {d : Nat}
    (hDistance : MiddleHomologyDistanceAtLeast (sourceChainComplex D) d) :
    MiddleHomologyDistanceAtLeast (chainComplex D) d := by sorry
