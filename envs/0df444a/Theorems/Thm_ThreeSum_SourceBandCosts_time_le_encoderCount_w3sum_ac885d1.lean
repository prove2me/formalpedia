-- Prove2me | Theorems.Thm_ThreeSum_SourceBandCosts_time_le_encoderCount_w3sum_ac885d1
-- name    : ThreeSum.SourceBandCosts.time_le_encoderCount_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:03:22.903192+00:00
-- url     : https://prove2.me/theorems/9648146c-6050-4f9d-b732-9397102ac534
-- title:
--   Source Band Costs: time le encoder Count
-- statement:
--   The Source Band Costs construction uses the time le encoder Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandCosts.lean#L126-L140
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandCosts.lean#L126-L140

import Definitions.Def_Submission_ThreeSum_LightSourceBandSetup
import Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts
import Mathlib.Data.Nat.Choose.Vandermonde
import Definitions.Def_Submission_ThreeSum_SourceBandCosts
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandCosts
open Scales TrimScales StageBounds CostLedger BandScales LocalCoverBounds

theorem ThreeSum.SourceBandCosts.time_le_encoderCount_w3sum_ac885d1 {N n p U D : ℕ} (hN : N ≤ n) :
    LightSourceBandSetup.time N (bandSize n) p
      (BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n))) U D ≤
      (1016*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+1946)*encoderCount n+560 := by sorry
