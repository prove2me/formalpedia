-- Prove2me | Theorems.Thm_ThreeSum_SourceBandCosts_persistent_space_le_encoderCount
-- name    : ThreeSum.SourceBandCosts.persistent_space_le_encoderCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:01:28.442571+00:00
-- url     : https://prove2.me/theorems/b7e3c626-1d68-4ea3-bf8d-8e549ae2bd91
-- title:
--   Source Band Costs: persistent space le encoder Count
-- statement:
--   The Source Band Costs construction uses the persistent space le encoder Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandCosts.lean#L142-L154
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandCosts.lean#L142-L154

import Definitions.Def_Submission_ThreeSum_LightSourceBandSetup
import Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts
import Mathlib.Data.Nat.Choose.Vandermonde
import Definitions.Def_Submission_ThreeSum_SourceBandCosts
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandCosts
open Scales TrimScales StageBounds CostLedger BandScales LocalCoverBounds

theorem ThreeSum.SourceBandCosts.persistent_space_le_encoderCount {base N n : ℕ} (hN : N ≤ n) :
    SourceBandLayout.work base N (bandSize n)
      (BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n))) ≤
      base+14*encoderCount n := by sorry
