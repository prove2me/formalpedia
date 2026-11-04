-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_swapEdge
-- name    : ThreeSum.TernaryCoverRegularity.left_swapEdge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:52:29.150128+00:00
-- url     : https://prove2.me/theorems/cd344ec8-6413-45c4-919a-86bcdfe7da28
-- title:
--   Ternary Cover Regularity: left swap Edge
-- statement:
--   The Ternary Cover Regularity construction uses the left swap Edge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRegularity.lean#L145-L146
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRegularity.lean#L145-L146

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverRegularity
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverRegularity
open Finset TernaryJointType TernaryCoverLocal
variable {L : ℕ}

theorem ThreeSum.TernaryCoverRegularity.left_swapEdge {α π : DigitType} (e : LocalEdge L α π) :
    left (swapEdge e) = right e := by sorry

attribute [defeq] ThreeSum.TernaryCoverRegularity.left_swapEdge
