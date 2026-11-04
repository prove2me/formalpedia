-- Prove2me | Theorems.Thm_ThreeSum_SourceControlCosts_span_word_bound
-- name    : ThreeSum.SourceControlCosts.span_word_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:51:12.767695+00:00
-- url     : https://prove2.me/theorems/d74cd6f9-92c9-4d00-a18b-73e2d306b781
-- title:
--   Source Control Costs: span word bound
-- statement:
--   The Source Control Costs construction uses the span word bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceControlCosts.lean#L19-L35
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceControlCosts.lean#L19-L35

import Definitions.Def_Submission_ThreeSum_LightSourceControlsHostProgram
import Definitions.Def_Submission_ThreeSum_SourceControlCosts
set_option autoImplicit false
open ThreeSum ThreeSum.SourceControlCosts
open Scales TrimScales StageBounds CostLedger BandScales

theorem ThreeSum.SourceControlCosts.span_word_bound {J W K S logP logE : ℕ} (hS : 0 < S) :
    SourceControlLayout.word J W K S logP logE ≤
      9*SourceControlLayout.span J W K S logP logE+30 := by sorry
