-- Prove2me | Theorems.Thm_ThreeSum_SourceFiniteCosts_time_le
-- name    : ThreeSum.SourceFiniteCosts.time_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:54:27.918804+00:00
-- url     : https://prove2.me/theorems/59eef9bb-8d80-4d0e-9958-0568963d3e7a
-- title:
--   Source Finite Costs: time le
-- statement:
--   The Source Finite Costs construction uses the time le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceFiniteCosts.lean#L35-L38
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceFiniteCosts.lean#L35-L38

import Definitions.Def_Submission_ThreeSum_SourceControlCosts
import Definitions.Def_Submission_ThreeSum_SourceFiniteCosts
import Theorems.Thm_ThreeSum_LightKaratsuba_time_le

set_option autoImplicit false
open ThreeSum ThreeSum.SourceFiniteCosts
open Scales TrimScales StageBounds CostLedger BandScales

theorem ThreeSum.SourceFiniteCosts.time_le {NL NR n p U D : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceControlsHost.time NL NR (bandSize n) p
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) U D ≤ time n p U D := by sorry
