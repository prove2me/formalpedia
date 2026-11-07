-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_boundary2_apply_inr
-- name    : QEC.Coding.DistanceBalancing.boundary2_apply_inr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:18:41.039193+00:00
-- url     : https://prove2.me/theorems/b914a254-03b9-4fb9-a123-ffd8dd1a6692
-- title:
--   Distance Balancing: boundary2 apply inr
-- statement:
--   The Distance Balancing construction uses the boundary2 apply inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L315-L322
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L315-L322

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

theorem QEC.Coding.DistanceBalancing.boundary2_apply_inr
    (w : Word (ZMod 2) (C2Index xTwo classicalBit))
    (x2 : xTwo) (b : classicalCheck) :
    boundary2 D w (Sum.inr (x2, b)) =
      ∑ a : classicalBit,
        D.classicalBoundary b a * xTwoBitSlice w a x2 := by sorry
