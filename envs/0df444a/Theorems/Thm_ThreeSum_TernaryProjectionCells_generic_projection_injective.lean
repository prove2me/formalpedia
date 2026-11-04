-- Prove2me | Theorems.Thm_ThreeSum_TernaryProjectionCells_generic_projection_injective
-- name    : ThreeSum.TernaryProjectionCells.generic_projection_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:46:27.271805+00:00
-- url     : https://prove2.me/theorems/4d7b4085-3dd3-425a-8831-adcf60ea2a89
-- title:
--   Ternary Projection Cells: generic projection injective
-- statement:
--   The Ternary Projection Cells construction uses the generic projection injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryProjectionCells.lean#L13-L32
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryProjectionCells.lean#L13-L32

import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryProjectionCells
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
open ThreeSum ThreeSum.TernaryProjectionCells
variable {K : Type*} [Field K]

theorem ThreeSum.TernaryProjectionCells.generic_projection_injective {a b : K}
    (ha : a ≠ 0) (hb : b ≠ 0) (h2 : (2 : K) ≠ 0)
    (hsum : a+b ≠ 0) (heq : a ≠ b) (hhalf : 2*a ≠ b) (hdouble : a ≠ 2*b) :
    Function.Injective (projectedCell a b) := by sorry
