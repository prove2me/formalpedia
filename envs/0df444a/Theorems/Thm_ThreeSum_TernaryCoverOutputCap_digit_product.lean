-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverOutputCap_digit_product
-- name    : ThreeSum.TernaryCoverOutputCap.digit_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:27:10.9273+00:00
-- url     : https://prove2.me/theorems/8a3d9414-b00c-4efb-835d-a582dce44958
-- title:
--   Ternary Cover Output Cap: digit product
-- statement:
--   The Ternary Cover Output Cap construction uses the digit product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverOutputCap.lean#L45-L59
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverOutputCap.lean#L45-L59

import Definitions.Def_Submission_ThreeSum_TernaryCoverRegularity
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverOutputCap
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverOutputCap
open Finset TernaryJointType TernaryCoverLocal
variable {L : ℕ}

theorem ThreeSum.TernaryCoverOutputCap.digit_product (q : TritWord L) :
    (∏ i, ((q i).val+1)) = 2^(digitCount q 1) * 3^(digitCount q 2) := by sorry
