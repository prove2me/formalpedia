-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverLayout_build_meets
-- name    : ThreeSum.LightLocalCoverLayout.build_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:26:46.18019+00:00
-- url     : https://prove2.me/theorems/7487ab20-b78f-409d-bcc3-03ab9b1db2b8
-- title:
--   Light Local Cover Layout: build meets
-- statement:
--   The Light Local Cover Layout construction uses the build meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverLayout.lean#L41-L56
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverLayout.lean#L41-L56

import Definitions.Def_Submission_ThreeSum_LightLocalCoverBuild
import Definitions.Def_Submission_ThreeSum_LightLocalCoverLayout
import Definitions.Def_WeightedCache3SUM_Alias_4eb33ef6f1e27fd8

set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverLayout
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables

theorem ThreeSum.LightLocalCoverLayout.build_meets {lim : Limits} {P : Program} {d pMain : ℕ}
    (S : LightLocalCoverBuild.Procs P pMain) {μ : ℕ → ℤ} {base h : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+512*h+7 ≤ lim.depth)
    (hspace : space base h ≤ lim.space) (hword : (LightLocalCoverBuild.word h : ℤ) ≤ lim.word) :
    Meets lim P pMain d
      [512*h,h,localPrime h,rows h,vertices h,localBucketCap h,base,bitPtr base h,maps base h,
        raw0 base h,raw1 base h,hist0 base h,hist1 base h,matrixPtr base h,work base h,
        scheduleSize h,scheduleMaps base h]
      μ (LightLocalCoverBuild.time h)
      (fun r ν => r = (scheduleMaps base h : ℤ) ∧
        Data ν h (maps base h) (hist0 base h) (hist1 base h) (matrixPtr base h) ∧
        ScheduleRows ν h (scheduleMaps base h) ∧
        (∀ s : Occurrence h, ν (candidates base h+s.val) = (candidateAt h s : ℤ)) ∧
        Kept μ ν base) := by sorry
