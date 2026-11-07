-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_transpose_boundary1_apply_inr
-- name    : QEC.Coding.DistanceBalancing.transpose_boundary1_apply_inr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:18:46.860413+00:00
-- url     : https://prove2.me/theorems/12d68687-3fa9-41ae-b1ef-25abad9138ef
-- title:
--   Distance Balancing: transpose boundary1 apply inr
-- statement:
--   The Distance Balancing construction uses the transpose boundary1 apply inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L354-L364
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L354-L364

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

theorem QEC.Coding.DistanceBalancing.transpose_boundary1_apply_inr
    (u : Word (ZMod 2)
      (C0Index xZero xOne classicalBit classicalCheck))
    (x2 : xTwo) (b : classicalCheck) :
    wordLinearMapTranspose (boundary1 D) u (Sum.inr (x2, b)) =
      ∑ x1 : xOne,
        D.xBoundary2 x1 x2 * u (Sum.inr (x1, b)) := by sorry
