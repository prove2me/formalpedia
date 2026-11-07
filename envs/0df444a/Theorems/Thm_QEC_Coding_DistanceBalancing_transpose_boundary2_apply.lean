-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_transpose_boundary2_apply
-- name    : QEC.Coding.DistanceBalancing.transpose_boundary2_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:17:59.997882+00:00
-- url     : https://prove2.me/theorems/7a3a1d5c-b5a3-4f90-96f1-60834d65483a
-- title:
--   Distance Balancing: transpose boundary2 apply
-- statement:
--   Coordinate formula for the transpose of the product's second boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L325-L338
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L325-L338

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

theorem QEC.Coding.DistanceBalancing.transpose_boundary2_apply
    (x : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (x2 : xTwo) (a : classicalBit) :
    wordLinearMapTranspose (boundary2 D) x (x2, a) =
      (∑ x1 : xOne,
        D.xBoundary2 x1 x2 * xOneBitSlice x a x1) +
      ∑ b : classicalCheck,
        D.classicalBoundary b a * xTwoCheckSlice x b x2 := by sorry
