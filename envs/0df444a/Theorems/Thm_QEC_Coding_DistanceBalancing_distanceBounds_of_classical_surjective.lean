-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_distanceBounds_of_classical_surjective
-- name    : QEC.Coding.DistanceBalancing.distanceBounds_of_classical_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:38:18.3902+00:00
-- url     : https://prove2.me/theorems/ed69d98f-4d97-41d3-8550-890797f044b7
-- title:
--   Distance Balancing: distance Bounds of classical surjective
-- statement:
--   The two finite EKZ20 distance conclusions in one assumption-minimal
--   interface.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L1430-L1448
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L1430-L1448

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

theorem QEC.Coding.DistanceBalancing.distanceBounds_of_classical_surjective
    (hSurjective : Function.Surjective
      (Matrix.toLin' D.classicalBoundary))
    {dHomology dCohomology dClassical : Nat}
    (hHomology : MiddleHomologyDistanceAtLeast
      (sourceChainComplex D) dHomology)
    (hCohomology : MiddleCohomologyDistanceAtLeast
      (sourceChainComplex D) dCohomology)
    (hClassical : ClassicalDistanceAtLeast
      D.classicalBoundary dClassical) :
    MiddleHomologyDistanceAtLeast
        (chainComplex D) (dClassical * dHomology) ∧
      MiddleCohomologyDistanceAtLeast
        (chainComplex D) dCohomology := by sorry
