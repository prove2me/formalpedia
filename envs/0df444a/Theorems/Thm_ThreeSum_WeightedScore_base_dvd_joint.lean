-- Prove2me | Theorems.Thm_ThreeSum_WeightedScore_base_dvd_joint
-- name    : ThreeSum.WeightedScore.base_dvd_joint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:19:13.0222+00:00
-- url     : https://prove2.me/theorems/d842f5d0-1b42-4b5f-b82e-612bfbe03c09
-- title:
--   Weighted Score: base dvd joint
-- statement:
--   The Weighted Score construction uses the base dvd joint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightedScore.lean#L43-L47
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightedScore.lean#L43-L47

import Definitions.Def_Submission_ThreeSum_WeightedModuli
import Definitions.Def_Submission_ThreeSum_ModuloCounts
import Definitions.Def_Submission_ThreeSum_WeightedScore
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedScore
open Finset Arithmetic ModuloCounts WeightedModuli
open scoped BigOperators

theorem ThreeSum.WeightedScore.base_dvd_joint (q p : ℕ) : q ∣ joint q p := by sorry
