-- Prove2me | Theorems.Thm_ThreeSum_LightBandPrimeStage_records_count_bound
-- name    : ThreeSum.LightBandPrimeStage.records_count_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:06:29.943956+00:00
-- url     : https://prove2.me/theorems/cd5d6652-7fde-4044-85dc-7368ec07f231
-- title:
--   Light Band Prime Stage: records count bound
-- statement:
--   The Light Band Prime Stage construction uses the records count bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandPrimeStage.lean#L45-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandPrimeStage.lean#L45-L53

import Definitions.Def_Submission_ThreeSum_BandPrimeCostBounds
import Definitions.Def_Submission_ThreeSum_BandRawAFinite
import Definitions.Def_Submission_ThreeSum_SourceBandCosts
import Definitions.Def_Submission_ThreeSum_LightBandPrimeStage
set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPrimeStage
open Light BandEnumeration BandCandidateRows Scales BandScales CostLedger
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

theorem ThreeSum.LightBandPrimeStage.records_count_bound {A B C : Family} {n nA nB nC : ℕ}
    (hA : A.size=BandPartition.size nA (bandSize n))
    (hB : B.size=BandPartition.size nB (bandSize n))
    (hC : C.size=BandPartition.size nC (bandSize n))
    (ha : nA ≤ n) (hb : nB ≤ n) (hc : nC ≤ n) :
    (records A B C).length ≤ 3*bandCount n^2 := by sorry
