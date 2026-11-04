-- Prove2me | Theorems.Thm_ThreeSum_TernaryMomentSchedule_channel_rows
-- name    : ThreeSum.TernaryMomentSchedule.channel_rows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:03:42.673458+00:00
-- url     : https://prove2.me/theorems/d353e270-a9c2-47a4-a50f-f8959a8ab3d1
-- title:
--   Ternary Moment Schedule: channel rows
-- statement:
--   The Ternary Moment Schedule construction uses the channel rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryMomentSchedule.lean#L41-L55
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryMomentSchedule.lean#L41-L55

import Definitions.Def_Submission_ThreeSum_TernaryWeightChannels
import Definitions.Def_Submission_ThreeSum_TernaryMomentSchedule
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryMomentSchedule
open Finset TernaryJointType
open scoped BigOperators

theorem ThreeSum.TernaryMomentSchedule.channel_rows (terms k i : ℕ) (score : ℕ→ℕ→ℕ→ℤ) :
    aggregate (channels terms) score k i=
      if k<terms then ∑ j∈range (k+1), score k j i else 0 := by sorry
