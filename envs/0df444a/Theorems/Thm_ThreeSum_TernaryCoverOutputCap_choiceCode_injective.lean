-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverOutputCap_choiceCode_injective
-- name    : ThreeSum.TernaryCoverOutputCap.choiceCode_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:27:15.951188+00:00
-- url     : https://prove2.me/theorems/6f9c30ed-5b04-4a5b-be2b-e38e53c671b6
-- title:
--   Ternary Cover Output Cap: choice Code injective
-- statement:
--   The Ternary Cover Output Cap construction uses the choice Code injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverOutputCap.lean#L19-L36
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverOutputCap.lean#L19-L36

import Definitions.Def_Submission_ThreeSum_TernaryCoverRegularity
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverOutputCap
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverOutputCap
open Finset TernaryJointType TernaryCoverLocal
variable {L : ℕ}

theorem ThreeSum.TernaryCoverOutputCap.choiceCode_injective (α π : DigitType) (q : TritWord L) :
    Function.Injective (choiceCode (α := α) (π := π) (q := q)) := by sorry
