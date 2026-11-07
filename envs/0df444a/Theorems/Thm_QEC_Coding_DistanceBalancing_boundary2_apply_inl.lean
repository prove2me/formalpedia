-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_boundary2_apply_inl
-- name    : QEC.Coding.DistanceBalancing.boundary2_apply_inl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:17:53.686539+00:00
-- url     : https://prove2.me/theorems/e5944ab5-c4b5-4be1-b17b-0df771f1f5d1
-- title:
--   Distance Balancing: boundary2 apply inl
-- statement:
--   The Distance Balancing construction uses the boundary2 apply inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L306-L313
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L306-L313

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

theorem QEC.Coding.DistanceBalancing.boundary2_apply_inl
    (w : Word (ZMod 2) (C2Index xTwo classicalBit))
    (x1 : xOne) (a : classicalBit) :
    boundary2 D w (Sum.inl (x1, a)) =
      ∑ x2 : xTwo,
        D.xBoundary2 x1 x2 * xTwoBitSlice w a x2 := by sorry
