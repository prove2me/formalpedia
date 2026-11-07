-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_boundary2_residualLift_apply_inr
-- name    : QEC.Coding.DistanceBalancing.boundary2_residualLift_apply_inr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:20:48.691365+00:00
-- url     : https://prove2.me/theorems/d12730f5-a23e-4672-9720-49482608f59c
-- title:
--   Distance Balancing: boundary2 residual Lift apply inr
-- statement:
--   The Distance Balancing construction uses the boundary2 residual Lift apply inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L1121-L1150
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L1121-L1150

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

theorem QEC.Coding.DistanceBalancing.boundary2_residualLift_apply_inr
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (hS : IsClassicalRightInverse D S)
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hFill : ∀ a : classicalBit,
      xOneBitSlice z a ∈ (sourceChainComplex D).middleBoundaryCode.carrier)
    (x2 : xTwo) (b : classicalCheck) :
    boundary2 D (residualLift D S z hFill) (Sum.inr (x2, b)) =
      sliceRemainder D z hFill (Sum.inr (x2, b)) := by sorry
