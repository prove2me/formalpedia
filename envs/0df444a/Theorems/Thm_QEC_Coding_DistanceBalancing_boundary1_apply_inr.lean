-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_boundary1_apply_inr
-- name    : QEC.Coding.DistanceBalancing.boundary1_apply_inr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:17:50.451686+00:00
-- url     : https://prove2.me/theorems/68f7ddab-ec53-4361-975a-3ddf33b4cd42
-- title:
--   Distance Balancing: boundary1 apply inr
-- statement:
--   The Distance Balancing construction uses the boundary1 apply inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L293-L304
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L293-L304

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

theorem QEC.Coding.DistanceBalancing.boundary1_apply_inr
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (x1 : xOne) (b : classicalCheck) :
    boundary1 D z (Sum.inr (x1, b)) =
      (∑ a : classicalBit,
        D.classicalBoundary b a * xOneBitSlice z a x1) +
      ∑ x2 : xTwo,
        D.xBoundary2 x1 x2 * xTwoCheckSlice z b x2 := by sorry
