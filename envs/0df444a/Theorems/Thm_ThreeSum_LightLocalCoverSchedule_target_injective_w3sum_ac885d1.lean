-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverSchedule_target_injective_w3sum_ac885d1
-- name    : ThreeSum.LightLocalCoverSchedule.target_injective_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:25:04.48496+00:00
-- url     : https://prove2.me/theorems/f8752849-0c1d-4837-b2a0-ad353fa7fe47
-- title:
--   Light Local Cover Schedule: target injective
-- statement:
--   The Light Local Cover Schedule construction uses the target injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverSchedule.lean#L31-L46
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverSchedule.lean#L31-L46

import Definitions.Def_Submission_ThreeSum_LightLocalCoverTransport
import Definitions.Def_Submission_ThreeSum_LocalCoverMatrix
import Definitions.Def_Submission_ThreeSum_WeightEnumeration
import Definitions.Def_Submission_ThreeSum_LightCoverGreedy
import Definitions.Def_Submission_ThreeSum_LightLocalCoverSchedule
set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverSchedule
open Finset LocalHashMoments LocalCoverBounds GlobalEncoding

theorem ThreeSum.LightLocalCoverSchedule.target_injective_w3sum_ac885d1 (h : ℕ) : Set.InjOn (target h) (range (cols h)) := by sorry
