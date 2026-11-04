-- Prove2me | Theorems.Thm_ThreeSum_EncodedColorPrimeCosts_count_le
-- name    : ThreeSum.EncodedColorPrimeCosts.count_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:23:37.735357+00:00
-- url     : https://prove2.me/theorems/3e79dc4f-9e92-4717-ae11-8665b874e5d9
-- title:
--   Encoded Color Prime Costs: count le
-- statement:
--   The Encoded Color Prime Costs construction uses the count le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorPrimeCosts.lean#L42-L51
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorPrimeCosts.lean#L42-L51

import Definitions.Def_Submission_ThreeSum_LightEncodedColorPrime
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeCosts
import Theorems.Thm_ThreeSum_ColorBandBounds_count_le
import Theorems.Thm_ThreeSum_LightHistogram_count_le
import Theorems.Thm_ThreeSum_LightSourceRowScan_count_le
import Theorems.Thm_ThreeSum_ModuloCounts_count_le

set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorPrimeCosts
open Light Scales BandScales CostLedger ArithmeticStageBounds

theorem ThreeSum.EncodedColorPrimeCosts.count_le {nA nB nC n : ℕ} (ha : nA ≤ n) (hb : nB ≤ n) (hc : nC ≤ n) :
    LightEncodedColorPrime.count nA nB nC (bandSize n) ≤ 3*bandCount n^2 := by sorry
