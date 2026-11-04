-- Prove2me | Theorems.Thm_ThreeSum_SourceFiniteData_source_ends
-- name    : ThreeSum.SourceFiniteData.source_ends
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:59:16.134254+00:00
-- url     : https://prove2.me/theorems/8cf24a94-e474-4a21-9817-a28118983879
-- title:
--   Source Finite Data: source ends
-- statement:
--   The Source Finite Data construction uses the source ends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorSourceRetention.lean#L9-L21
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorSourceRetention.lean#L9-L21

import Definitions.Def_Submission_ThreeSum_SourceFiniteData
import Definitions.Def_Submission_ThreeSum_EncodedColorSourceRetention
import Theorems.Thm_Light_Ends_next

set_option autoImplicit false
open ThreeSum ThreeSum.SourceFiniteData
open Light

theorem ThreeSum.SourceFiniteData.source_ends (base NL NR g h J cut : ℕ) :
    base+3 ≤ LightSourceControlsHost.finish base NL NR g h J cut ∧
    SourceBandPairData.next (LightSourceControlsHost.sourceBase base) NL NR g
      (BlockSourceEncoding.modulus h J) ≤ LightSourceControlsHost.finish base NL NR g h J cut ∧
    LightSourceBandHost.bankHeader (LightSourceControlsHost.sourceBase base) NL NR g h J+5 ≤
      LightSourceControlsHost.finish base NL NR g h J cut := by sorry
