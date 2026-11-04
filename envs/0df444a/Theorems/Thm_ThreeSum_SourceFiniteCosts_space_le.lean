-- Prove2me | Theorems.Thm_ThreeSum_SourceFiniteCosts_space_le
-- name    : ThreeSum.SourceFiniteCosts.space_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:55:16.568982+00:00
-- url     : https://prove2.me/theorems/0daa60c2-57d3-4e78-8a74-09b99c214012
-- title:
--   Source Finite Costs: space le
-- statement:
--   The Source Finite Costs construction uses the space le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceFiniteCosts.lean#L40-L43
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceFiniteCosts.lean#L40-L43

import Definitions.Def_Submission_ThreeSum_SourceControlCosts
import Definitions.Def_Submission_ThreeSum_SourceFiniteCosts
set_option autoImplicit false
open ThreeSum ThreeSum.SourceFiniteCosts
open Scales TrimScales StageBounds CostLedger BandScales

theorem ThreeSum.SourceFiniteCosts.space_le {base NL NR n p U D : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceControlsHost.space base NL NR (bandSize n) p
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) U D ≤ space base n p U D := by sorry
