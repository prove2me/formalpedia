-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_boundary2_productSliceFilling_apply_inl
-- name    : QEC.Coding.DistanceBalancing.boundary2_productSliceFilling_apply_inl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:20:33.643263+00:00
-- url     : https://prove2.me/theorems/37474bb8-da28-4a8d-883a-7818e058c4be
-- title:
--   Distance Balancing: boundary2 product Slice Filling apply inl
-- statement:
--   The Distance Balancing construction uses the boundary2 product Slice Filling apply inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L1035-L1046
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L1035-L1046

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

theorem QEC.Coding.DistanceBalancing.boundary2_productSliceFilling_apply_inl
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hFill : ∀ a : classicalBit,
      xOneBitSlice z a ∈ (sourceChainComplex D).middleBoundaryCode.carrier)
    (x1 : xOne) (a : classicalBit) :
    boundary2 D (productSliceFilling D z hFill) (Sum.inl (x1, a)) =
      z (Sum.inl (x1, a)) := by sorry
