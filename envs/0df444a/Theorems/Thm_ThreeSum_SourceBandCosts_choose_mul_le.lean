-- Prove2me | Theorems.Thm_ThreeSum_SourceBandCosts_choose_mul_le
-- name    : ThreeSum.SourceBandCosts.choose_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:03:55.040085+00:00
-- url     : https://prove2.me/theorems/52e4fabb-f711-4c8c-9a04-2177d3f79858
-- title:
--   Source Band Costs: choose mul le
-- statement:
--   The Source Band Costs construction uses the choose mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandCosts.lean#L11-L14
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandCosts.lean#L11-L14

import Definitions.Def_Submission_ThreeSum_LightSourceBandSetup
import Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts
import Mathlib.Data.Nat.Choose.Vandermonde
import Definitions.Def_Submission_ThreeSum_SourceBandCosts
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandCosts
open Scales TrimScales StageBounds CostLedger BandScales LocalCoverBounds

theorem ThreeSum.SourceBandCosts.choose_mul_le (L K N M : ℕ) : L.choose K*N.choose M ≤ (L+N).choose (K+M) := by sorry
