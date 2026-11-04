-- Prove2me | Theorems.Thm_ThreeSum_TernaryProjectionCells_collision_classification
-- name    : ThreeSum.TernaryProjectionCells.collision_classification
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:56:11.691055+00:00
-- url     : https://prove2.me/theorems/9d77b2ee-b6da-4db7-8275-be82aea69803
-- title:
--   Ternary Projection Cells: collision classification
-- statement:
--   The Ternary Projection Cells construction uses the collision classification property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryProjectionCells.lean#L34-L40
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryProjectionCells.lean#L34-L40

import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryProjectionCells
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
open ThreeSum ThreeSum.TernaryProjectionCells
variable {K : Type*} [Field K]

theorem ThreeSum.TernaryProjectionCells.collision_classification {a b : K}
    (ha : a ≠ 0) (hb : b ≠ 0) (h2 : (2 : K) ≠ 0)
    {i j : Fin 6} (hij : i ≠ j) (h : projectedCell a b i = projectedCell a b j) :
    a+b = 0 ∨ a = b ∨ 2*a = b ∨ a = 2*b := by sorry
