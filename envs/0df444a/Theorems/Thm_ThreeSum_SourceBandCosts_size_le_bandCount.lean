-- Prove2me | Theorems.Thm_ThreeSum_SourceBandCosts_size_le_bandCount
-- name    : ThreeSum.SourceBandCosts.size_le_bandCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:01:02.360779+00:00
-- url     : https://prove2.me/theorems/4152e312-620d-45c4-a4cd-32dbcf1e7af0
-- title:
--   Source Band Costs: size le band Count
-- statement:
--   The Source Band Costs construction uses the size le band Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandCosts.lean#L114-L124
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandCosts.lean#L114-L124

import Definitions.Def_Submission_ThreeSum_LightSourceBandSetup
import Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts
import Mathlib.Data.Nat.Choose.Vandermonde
import Definitions.Def_Submission_ThreeSum_SourceBandCosts
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandCosts
open Scales TrimScales StageBounds CostLedger BandScales LocalCoverBounds

theorem ThreeSum.SourceBandCosts.size_le_bandCount {N n : ℕ} (hN : N ≤ n) : BandPartition.size N (bandSize n) ≤ bandCount n := by sorry
