-- Prove2me | Theorems.Thm_ThreeSum_SourceFiniteCosts_word_le
-- name    : ThreeSum.SourceFiniteCosts.word_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:56:00.910459+00:00
-- url     : https://prove2.me/theorems/f3a25be6-6ca6-45db-ac75-d94712719b7a
-- title:
--   Source Finite Costs: word le
-- statement:
--   The Source Finite Costs construction uses the word le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceFiniteCosts.lean#L50-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceFiniteCosts.lean#L50-L53

import Definitions.Def_Submission_ThreeSum_SourceControlCosts
import Definitions.Def_Submission_ThreeSum_SourceFiniteCosts
set_option autoImplicit false
open ThreeSum ThreeSum.SourceFiniteCosts
open Scales TrimScales StageBounds CostLedger BandScales

theorem ThreeSum.SourceFiniteCosts.word_le {NL NR n p U D : ℕ} (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceControlsHost.word NL NR (bandSize n) p
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) U D ≤ word n p U D := by sorry
