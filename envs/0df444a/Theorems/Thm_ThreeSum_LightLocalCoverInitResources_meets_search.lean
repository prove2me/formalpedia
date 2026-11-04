-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverInitResources_meets_search
-- name    : ThreeSum.LightLocalCoverInitResources.meets_search
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:12:14.554892+00:00
-- url     : https://prove2.me/theorems/ab3604d4-10cc-4c3f-ad98-5827446d6005
-- title:
--   Light Local Cover Init Resources: meets search
-- statement:
--   Actual parameter selection and exact local cover from only h and free.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverInitResources.lean#L99-L117
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverInitResources.lean#L99-L117

import Definitions.Def_Submission_ThreeSum_LightLocalCoverInit
import Definitions.Def_Submission_ThreeSum_LightLocalCoverResources
import Definitions.Def_Submission_ThreeSum_LightLocalCoverInitResources
import Theorems.Thm_ThreeSum_LightLocalCoverResources_meets_search

set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverInitResources
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout
set_option maxHeartbeats 1500000

theorem ThreeSum.LightLocalCoverInitResources.meets_search {lim : Limits} {P : Program} {d pMain n free : ℕ}
    {μ : ℕ → ℤ} (S : LightLocalCoverInit.Procs P pMain)
    (hh : 1 ≤ Scales.microHalf (Scales.inputBits n))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : d+Scales.localSearch 5000000 n ≤ lim.depth)
    (hspace : free+Scales.localSearch 5000000 n ≤ lim.space)
    (hword : (Scales.localSearch 5000000 n : ℤ) ≤ lim.word) :
    let h := Scales.microHalf (Scales.inputBits n)
    let base := LightLocalCoverInit.base free
    Meets lim P pMain d [h,free] μ (Scales.localSearch 5000000 n)
      (fun r ν => r = (LightLocalCoverMetadata.nextFree base h : ℤ) ∧
        Seg ν free (LightLocalCoverInit.values free h) ∧
        Data ν h (maps base h) (hist0 base h) (hist1 base h) (matrixPtr base h) ∧
        ScheduleRows ν h (scheduleMaps base h) ∧
        (∀ s : Occurrence h, ν (candidates base h+s.val) = (candidateAt h s : ℤ)) ∧
        Kept μ ν free) := by sorry
