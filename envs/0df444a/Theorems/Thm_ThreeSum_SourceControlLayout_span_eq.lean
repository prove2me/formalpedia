-- Prove2me | Theorems.Thm_ThreeSum_SourceControlLayout_span_eq
-- name    : ThreeSum.SourceControlLayout.span_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:35:08.020868+00:00
-- url     : https://prove2.me/theorems/2f00d02a-89e4-42dd-a346-e63a75fa8423
-- title:
--   Source Control Layout: span eq
-- statement:
--   The Source Control Layout construction uses the span eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceControlLayout.lean#L34-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceControlLayout.lean#L34-L39

import Definitions.Def_Submission_ThreeSum_SourceBandBanksCosts
import Definitions.Def_Submission_ThreeSum_SourceControlLayout
import Theorems.Thm_ThreeSum_SourceBandBanksCosts_span_eq

set_option autoImplicit false
open ThreeSum ThreeSum.SourceControlLayout
open GlobalEncoding LocalCoverBounds BlockSourceEncoding SubsetAddress

theorem ThreeSum.SourceControlLayout.span_eq (h J cut : ℕ) :
    span J (J*(512*h)) (downsetCap (J*(512*h)) cut) (LightBlockSourceCatalog.count h J)
      (Nat.log 2 ((512*h)*localPrime h+1)) (Nat.log 2 (LightBlockSourceBuild.endpointBound h J+1)) =
      SourceBandBankLayout.span h J cut := by sorry
