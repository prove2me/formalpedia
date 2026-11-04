-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverInitResources_program_meets_search
-- name    : ThreeSum.LightLocalCoverInitResources.program_meets_search
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:08:26.139202+00:00
-- url     : https://prove2.me/theorems/d443849e-57f7-49ee-852c-d7df8741dc7a
-- title:
--   Light Local Cover Init Resources: program meets search
-- statement:
--   The closed fixed program has no supplied procedure or data oracle.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverInitResources.lean#L121-L136
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverInitResources.lean#L121-L136

import Definitions.Def_Submission_ThreeSum_LightLocalCoverInit
import Definitions.Def_Submission_ThreeSum_LightLocalCoverResources
import Definitions.Def_Submission_ThreeSum_LightLocalCoverInitResources
set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverInitResources
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout
set_option maxHeartbeats 1500000

theorem ThreeSum.LightLocalCoverInitResources.program_meets_search {lim : Limits} {d n free : ℕ} {μ : ℕ → ℤ}
    (hh : 1 ≤ Scales.microHalf (Scales.inputBits n))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : d+Scales.localSearch 5000000 n ≤ lim.depth)
    (hspace : free+Scales.localSearch 5000000 n ≤ lim.space)
    (hword : (Scales.localSearch 5000000 n : ℤ) ≤ lim.word) :
    let h := Scales.microHalf (Scales.inputBits n)
    let base := LightLocalCoverInit.base free
    Meets lim LightLocalCoverInit.program 52 d [h,free] μ (Scales.localSearch 5000000 n)
      (fun r ν => r = (LightLocalCoverMetadata.nextFree base h : ℤ) ∧
        Seg ν free (LightLocalCoverInit.values free h) ∧
        Data ν h (maps base h) (hist0 base h) (hist1 base h) (matrixPtr base h) ∧
        ScheduleRows ν h (scheduleMaps base h) ∧
        (∀ s : Occurrence h, ν (candidates base h+s.val) = (candidateAt h s : ℤ)) ∧
        Kept μ ν free) := by sorry
