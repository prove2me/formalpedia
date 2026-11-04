-- Prove2me | Theorems.Thm_ThreeSum_SourceFiniteCosts_finish_le
-- name    : ThreeSum.SourceFiniteCosts.finish_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:56:08.814317+00:00
-- url     : https://prove2.me/theorems/23a9a34e-6d81-4ba5-87e9-acb1e7155078
-- title:
--   Source Finite Costs: finish le
-- statement:
--   The Source Finite Costs construction uses the finish le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceFiniteCosts.lean#L45-L48
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceFiniteCosts.lean#L45-L48

import Definitions.Def_Submission_ThreeSum_SourceControlCosts
import Definitions.Def_Submission_ThreeSum_SourceFiniteCosts
set_option autoImplicit false
open ThreeSum ThreeSum.SourceFiniteCosts
open Scales TrimScales StageBounds CostLedger BandScales

theorem ThreeSum.SourceFiniteCosts.finish_le {base NL NR n : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceControlsHost.finish base NL NR (bandSize n)
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) ≤ finish base n := by sorry
