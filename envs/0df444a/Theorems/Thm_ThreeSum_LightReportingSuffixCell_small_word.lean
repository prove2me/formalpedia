-- Prove2me | Theorems.Thm_ThreeSum_LightReportingSuffixCell_small_word
-- name    : ThreeSum.LightReportingSuffixCell.small_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:23:21.074558+00:00
-- url     : https://prove2.me/theorems/cc59f856-48c2-4a12-bb19-e814c904b0c6
-- title:
--   Light Reporting Suffix Cell: small word
-- statement:
--   The Light Reporting Suffix Cell construction uses the small word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSuffixCell.lean#L26-L32
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSuffixCell.lean#L26-L32

import Definitions.Def_Submission_ThreeSum_ReportingHostSuffix
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixCell
set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingSuffixCell
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open LightZetaCell ReportingHostSuffix
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightReportingSuffixCell.small_word {W V : ℕ} (hV : V ≤ W)
    (hw : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word) :
    (((V+1)*2^(V+1) : ℕ) : ℤ) ≤ lim.word := by sorry
