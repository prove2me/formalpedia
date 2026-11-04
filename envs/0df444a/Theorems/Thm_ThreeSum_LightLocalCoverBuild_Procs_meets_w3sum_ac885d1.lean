-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverBuild_Procs_meets_w3sum_ac885d1
-- name    : ThreeSum.LightLocalCoverBuild.Procs.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:36:05.671659+00:00
-- url     : https://prove2.me/theorems/691b7e41-4070-4da8-bdd4-0e3ff105f1bd
-- title:
--   Procs: meets
-- statement:
--   The Procs construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverBuild.lean#L51-L138
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverBuild.lean#L51-L138

import Definitions.Def_Submission_ThreeSum_LightLocalCoverHost
import Definitions.Def_Submission_ThreeSum_LightSubsetEnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightMaskBitTable
import Definitions.Def_Submission_ThreeSum_LightLocalCoverBuild
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_f318d8b49c9fc733
import Definitions.Def_WeightedCache3SUM_Alias_2b9c97c844160a97
import Theorems.Thm_ThreeSum_LightCoverSelect_Procs_meets
import Theorems.Thm_ThreeSum_LightCoverSelect_meets
import Definitions.Def_WeightedCache3SUM_Alias_7c6295bca57f98dc
import Theorems.Thm_ThreeSum_LightHashHistogram_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_d5eaa25d4585cc6b
import Definitions.Def_WeightedCache3SUM_Alias_da105011ac4dcdd4
import Definitions.Def_WeightedCache3SUM_Alias_942628883105a84f
import Definitions.Def_WeightedCache3SUM_Alias_04fc0611b78e7896
import Definitions.Def_WeightedCache3SUM_Alias_a64b3be7ea8b7b19
import Definitions.Def_WeightedCache3SUM_Alias_ed969675cd1be1e3
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_e1d95931a2ead3e4
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Definitions.Def_WeightedCache3SUM_Alias_9176929b72776235
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Theorems.Thm_ThreeSum_LightScaleArray_meets
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Definitions.Def_WeightedCache3SUM_Alias_f29d07b5f5ce2e2c
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Definitions.Def_WeightedCache3SUM_Alias_66dd70707634c020
import Definitions.Def_WeightedCache3SUM_Alias_cdc5e7727f35fd80
import Definitions.Def_WeightedCache3SUM_Alias_de9d37b5900d1a92
import Definitions.Def_WeightedCache3SUM_Alias_a495b72bdff1a7b5
import Definitions.Def_WeightedCache3SUM_Alias_b5410f4bcc10d599

set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverBuild
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
set_option maxHeartbeats 1500000
set_option maxRecDepth 6000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightLocalCoverBuild.Procs.meets_w3sum_ac885d1 {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {h masks bitPtr maps raw0 raw1 hist0 hist1 matrixPtr work scheduleMaps : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+512*h+7 ≤ lim.depth)
    (hspace : LightLocalCoverCandidate.space work (512*h)
      (LocalMaskGraph.vertexCount (512*h) h) (localPrime h) ≤ lim.space)
    (hmasks : masks+LocalMaskGraph.vertexCount (512*h) h ≤ bitPtr)
    (hbits : bitPtr+LocalMaskGraph.vertexCount (512*h) h*(512*h) ≤ maps)
    (hmaps : maps+rows h*(2*(512*h)) ≤ raw0)
    (hraw0 : raw0+2*LocalMaskGraph.vertexCount (512*h) h ≤ raw1)
    (hraw1 : raw1+2*LocalMaskGraph.vertexCount (512*h) h ≤ hist0)
    (hhist0 : hist0+rows h*localPrime h ≤ hist1)
    (hhist1 : hist1+rows h*localPrime h ≤ matrixPtr)
    (hmatrix : matrixPtr+rows h*cols h ≤ work)
    (hschedule : work+LightCoverGreedy.total (rows h) (cols h) (scheduleSize h) ≤ scheduleMaps)
    (houtSpace : scheduleMaps+scheduleSize h*(2*(512*h)) ≤ lim.space)
    (hword : (word h : ℤ) ≤ lim.word) :
    Meets lim P pMain d
      [512*h,h,localPrime h,rows h,LocalMaskGraph.vertexCount (512*h) h,localBucketCap h,
        masks,bitPtr,maps,raw0,raw1,hist0,hist1,matrixPtr,work,scheduleSize h,scheduleMaps]
      μ (time h)
      (fun r ν => r = (scheduleMaps : ℤ) ∧
        Data ν h maps hist0 hist1 matrixPtr ∧ ScheduleRows ν h scheduleMaps ∧
        (∀ s : Occurrence h,
          ν (LightCoverGreedy.out work (rows h) (cols h)+s.val) = (candidateAt h s : ℤ)) ∧
        Kept μ ν masks) := by sorry
