-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_swapEdge
-- name    : ThreeSum.TernaryCoverRegularity.right_swapEdge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:52:23.948856+00:00
-- url     : https://prove2.me/theorems/cda12a73-e4cc-4ebe-b97f-6fecdf188606
-- title:
--   Ternary Cover Regularity: right swap Edge
-- statement:
--   The Ternary Cover Regularity construction uses the right swap Edge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRegularity.lean#L147-L148
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRegularity.lean#L147-L148

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverRegularity
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverRegularity
open Finset TernaryJointType TernaryCoverLocal
variable {L : ℕ}

theorem ThreeSum.TernaryCoverRegularity.right_swapEdge {α π : DigitType} (e : LocalEdge L α π) :
    right (swapEdge e) = left e := by sorry

attribute [defeq] ThreeSum.TernaryCoverRegularity.right_swapEdge
