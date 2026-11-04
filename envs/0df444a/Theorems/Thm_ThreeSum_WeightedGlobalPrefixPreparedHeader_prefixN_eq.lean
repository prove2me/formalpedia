-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPrefixPreparedHeader_prefixN_eq
-- name    : ThreeSum.WeightedGlobalPrefixPreparedHeader.prefixN_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:02:18.015279+00:00
-- url     : https://prove2.me/theorems/78ecc6ca-e0fc-42cc-bca0-c16418ebc096
-- title:
--   Weighted Global Prefix Prepared Header: prefix N eq
-- statement:
--   The Weighted Global Prefix Prepared Header construction uses the prefix N eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixPreparedHeader.lean#L18-L20
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixPreparedHeader.lean#L18-L20

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaHeaderAgreement
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixPrepare
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixPreparedHeader
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPrefixPreparedHeader
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaHeaderAgreement
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {p m F : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalPrefixPreparedHeader.prefixN_eq (m r : ℕ) : LightWeightedGlobalPrefixSetup.N m r=N m r := by sorry
