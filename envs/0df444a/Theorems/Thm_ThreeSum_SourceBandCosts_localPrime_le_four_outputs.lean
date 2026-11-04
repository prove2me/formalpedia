-- Prove2me | Theorems.Thm_ThreeSum_SourceBandCosts_localPrime_le_four_outputs
-- name    : ThreeSum.SourceBandCosts.localPrime_le_four_outputs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:01:36.809895+00:00
-- url     : https://prove2.me/theorems/5e781e3f-dd61-4fd8-81a8-e6b4db28cca7
-- title:
--   Source Band Costs: local Prime le four outputs
-- statement:
--   The Source Band Costs construction uses the local Prime le four outputs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandCosts.lean#L42-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandCosts.lean#L42-L49

import Definitions.Def_Submission_ThreeSum_LightSourceBandSetup
import Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts
import Mathlib.Data.Nat.Choose.Vandermonde
import Definitions.Def_Submission_ThreeSum_SourceBandCosts
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandCosts
open Scales TrimScales StageBounds CostLedger BandScales LocalCoverBounds

theorem ThreeSum.SourceBandCosts.localPrime_le_four_outputs (h : ℕ) : localPrime h ≤ 4*outputCount (512*h) h := by sorry
