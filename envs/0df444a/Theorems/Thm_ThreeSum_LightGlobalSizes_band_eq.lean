-- Prove2me | Theorems.Thm_ThreeSum_LightGlobalSizes_band_eq
-- name    : ThreeSum.LightGlobalSizes.band_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:03:58.183725+00:00
-- url     : https://prove2.me/theorems/b726a4f5-9397-429a-a578-b679492143b7
-- title:
--   Light Global Sizes: band eq
-- statement:
--   The Light Global Sizes construction uses the band eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightGlobalSizes.lean#L164-L164
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightGlobalSizes.lean#L164-L164

import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSum_BandScales
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Sqrt
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSum_LightGlobalSizes
set_option autoImplicit false
open ThreeSum ThreeSum.LightGlobalSizes
set_option maxHeartbeats 1000000
open Light LocalCoverBounds
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightGlobalSizes.band_eq (C J mu : ℕ) : band C J mu = root C J ⌈/⌉ divisor mu := by sorry
