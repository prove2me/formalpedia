-- Prove2me | Theorems.Thm_ThreeSum_WeightedScore_joint_count_le
-- name    : ThreeSum.WeightedScore.joint_count_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:19:16.431292+00:00
-- url     : https://prove2.me/theorems/d8e58510-748c-4759-9285-6eff40132fd1
-- title:
--   Weighted Score: joint count le
-- statement:
--   The Weighted Score construction uses the joint count le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightedScore.lean#L49-L51
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightedScore.lean#L49-L51

import Definitions.Def_Submission_ThreeSum_WeightedModuli
import Definitions.Def_Submission_ThreeSum_ModuloCounts
import Definitions.Def_Submission_ThreeSum_WeightedScore
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedScore
open Finset Arithmetic ModuloCounts WeightedModuli
open scoped BigOperators

theorem ThreeSum.WeightedScore.joint_count_le (q p nA nB nC : ℕ) (a b c : ℕ → ℤ) :
    count (joint q p) nA nB nC a b c ≤ count q nA nB nC a b c := by sorry
