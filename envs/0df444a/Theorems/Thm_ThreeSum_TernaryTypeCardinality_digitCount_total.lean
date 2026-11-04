-- Prove2me | Theorems.Thm_ThreeSum_TernaryTypeCardinality_digitCount_total
-- name    : ThreeSum.TernaryTypeCardinality.digitCount_total
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:50:46.282507+00:00
-- url     : https://prove2.me/theorems/9b200d57-85c7-4313-a8cd-5149eb387860
-- title:
--   Ternary Type Cardinality: digit Count total
-- statement:
--   The Ternary Type Cardinality construction uses the digit Count total property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTypeCardinality.lean#L30-L38
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTypeCardinality.lean#L30-L38

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sigma
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryTypeCardinality
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryCoverLocal
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryTypeCardinality.digitCount_total {L : ℕ} (w : TritWord L) :
    digitCount w 0+digitCount w 1+digitCount w 2=L := by sorry
