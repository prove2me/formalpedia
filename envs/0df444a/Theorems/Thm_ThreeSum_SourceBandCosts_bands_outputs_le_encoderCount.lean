-- Prove2me | Theorems.Thm_ThreeSum_SourceBandCosts_bands_outputs_le_encoderCount
-- name    : ThreeSum.SourceBandCosts.bands_outputs_le_encoderCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:03:33.044549+00:00
-- url     : https://prove2.me/theorems/13389570-1070-4d42-ad44-a1ffc928f36a
-- title:
--   Source Band Costs: bands outputs le encoder Count
-- statement:
--   The Source Band Costs construction uses the bands outputs le encoder Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandCosts.lean#L86-L92
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandCosts.lean#L86-L92

import Definitions.Def_Submission_ThreeSum_LightSourceBandSetup
import Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts
import Mathlib.Data.Nat.Choose.Vandermonde
import Definitions.Def_Submission_ThreeSum_SourceBandCosts
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandCosts
open Scales TrimScales StageBounds CostLedger BandScales LocalCoverBounds

theorem ThreeSum.SourceBandCosts.bands_outputs_le_encoderCount (n : ℕ) : bandCount n*fullOutputs n ≤ encoderCount n := by sorry
