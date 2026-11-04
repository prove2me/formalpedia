-- Prove2me | Theorems.Thm_ThreeSum_SourceBandCosts_choose_pow_le
-- name    : ThreeSum.SourceBandCosts.choose_pow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:00:59.204195+00:00
-- url     : https://prove2.me/theorems/04cf48e5-0a5e-4b9f-ba98-773d52303f80
-- title:
--   Source Band Costs: choose pow le
-- statement:
--   The Source Band Costs construction uses the choose pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandCosts.lean#L16-L24
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandCosts.lean#L16-L24

import Definitions.Def_Submission_ThreeSum_LightSourceBandSetup
import Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts
import Mathlib.Data.Nat.Choose.Vandermonde
import Definitions.Def_Submission_ThreeSum_SourceBandCosts
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandCosts
open Scales TrimScales StageBounds CostLedger BandScales LocalCoverBounds

theorem ThreeSum.SourceBandCosts.choose_pow_le (L K J : ℕ) : (L.choose K)^J ≤ (J*L).choose (J*K) := by sorry
