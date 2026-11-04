-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverRegularity_swapEdge_injective
-- name    : ThreeSum.TernaryCoverRegularity.swapEdge_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:27:18.048037+00:00
-- url     : https://prove2.me/theorems/83725f10-d577-42bb-a9d2-465a1a901b83
-- title:
--   Ternary Cover Regularity: swap Edge injective
-- statement:
--   The Ternary Cover Regularity construction uses the swap Edge injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRegularity.lean#L152-L154
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRegularity.lean#L152-L154

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverRegularity
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverRegularity
open Finset TernaryJointType TernaryCoverLocal
variable {L : ℕ}

theorem ThreeSum.TernaryCoverRegularity.swapEdge_injective (α π : DigitType) :
    Function.Injective (swapEdge (α := α) (π := π) (L := L)) := by sorry
