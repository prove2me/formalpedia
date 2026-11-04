-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverResources_meets_search
-- name    : ThreeSum.LightLocalCoverResources.meets_search
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:21:12.018091+00:00
-- url     : https://prove2.me/theorems/5a739ae3-89d4-4bb7-addf-5b148f9f3580
-- title:
--   Light Local Cover Resources: meets search
-- statement:
--   The fully constructed exact local cover under one uniform search budget.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverResources.lean#L205-L222
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverResources.lean#L205-L222

import Definitions.Def_Submission_ThreeSum_LightLocalCoverSetup
import Definitions.Def_Submission_ThreeSum_LightLocalCoverCost
import Definitions.Def_Submission_ThreeSum_LightLocalCoverMagnitude
import Definitions.Def_Submission_ThreeSum_LightLocalCoverResources
set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverResources
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout LightLocalCoverMagnitude
set_option maxHeartbeats 1800000

theorem ThreeSum.LightLocalCoverResources.meets_search {lim : Limits} {P : Program} {d pMain n base : ℕ}
    {μ : ℕ → ℤ} (S : LightLocalCoverSetup.Procs P pMain)
    (hh : 1 ≤ Scales.microHalf (Scales.inputBits n))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : d+Scales.localSearch 4000000 n ≤ lim.depth)
    (hspace : base+Scales.localSearch 4000000 n ≤ lim.space)
    (hword : (Scales.localSearch 4000000 n : ℤ) ≤ lim.word) :
    let h := Scales.microHalf (Scales.inputBits n)
    Meets lim P pMain d [h,localPrime h,vertices h,localBucketCap h,base]
      μ (Scales.localSearch 4000000 n)
      (fun r ν => r = (scheduleMaps base h : ℤ) ∧
        Data ν h (maps base h) (hist0 base h) (hist1 base h) (matrixPtr base h) ∧
        ScheduleRows ν h (scheduleMaps base h) ∧
        (∀ s : Occurrence h, ν (candidates base h+s.val) = (candidateAt h s : ℤ)) ∧
        Kept μ ν base) := by sorry
