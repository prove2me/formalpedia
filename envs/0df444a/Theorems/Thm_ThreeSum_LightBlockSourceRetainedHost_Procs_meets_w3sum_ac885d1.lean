-- Prove2me | Theorems.Thm_ThreeSum_LightBlockSourceRetainedHost_Procs_meets_w3sum_ac885d1
-- name    : ThreeSum.LightBlockSourceRetainedHost.Procs.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:57:18.9452+00:00
-- url     : https://prove2.me/theorems/cfcccd9c-2707-442f-a26b-509a70ccf50d
-- title:
--   Procs: meets
-- statement:
--   The Procs construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceRetainedHost.lean#L66-L217
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceRetainedHost.lean#L66-L217

import Definitions.Def_Submission_ThreeSum_LightBlockSourceRetainedStages
import Definitions.Def_Submission_ThreeSum_LightBlockSourcePreparation
import Definitions.Def_Submission_ThreeSum_LightDownsetEnumerationSetup
import Definitions.Def_Submission_ThreeSum_BlockSourceCoverInput
import Definitions.Def_Submission_ThreeSum_LightBlockSourceRetainedHost
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Definitions.Def_WeightedCache3SUM_Alias_244efc85702348f3
import Definitions.Def_WeightedCache3SUM_Alias_5f0dc31657648884
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_f318d8b49c9fc733
import Definitions.Def_WeightedCache3SUM_Alias_2b9c97c844160a97
import Theorems.Thm_ThreeSum_LightCoverSelect_Procs_meets
import Theorems.Thm_ThreeSum_LightCoverSelect_meets
import Definitions.Def_WeightedCache3SUM_Alias_7c6295bca57f98dc
import Definitions.Def_WeightedCache3SUM_Alias_f8e3ce9eb3f48862
import Definitions.Def_WeightedCache3SUM_Alias_2ae6d2b4167e20c4
import Definitions.Def_WeightedCache3SUM_Alias_31257a44f822c74e
import Theorems.Thm_ThreeSum_LightHashHistogram_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_d5eaa25d4585cc6b
import Definitions.Def_WeightedCache3SUM_Alias_da105011ac4dcdd4
import Definitions.Def_WeightedCache3SUM_Alias_04fc0611b78e7896
import Definitions.Def_WeightedCache3SUM_Alias_a64b3be7ea8b7b19
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
import Theorems.Thm_ThreeSum_LightSourceBuild_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_bff01fd4b2900a53
import Definitions.Def_WeightedCache3SUM_Alias_8f9b8fc511f535d5
import Definitions.Def_WeightedCache3SUM_Alias_27f79aa230fbddf9
import Definitions.Def_WeightedCache3SUM_Alias_5b14bc7229a63f1e
import Definitions.Def_WeightedCache3SUM_Alias_4bb45babfe810a30
import Definitions.Def_WeightedCache3SUM_Alias_a076d5b93ecac4d9
import Theorems.Thm_ThreeSum_LightSourceResidues_meets
import Definitions.Def_WeightedCache3SUM_Alias_ce5ff1e60c39fd21
import Definitions.Def_WeightedCache3SUM_Alias_e80b8f80e26e0eba
import Definitions.Def_WeightedCache3SUM_Alias_d4ec36c7dcd9fa6e
import Theorems.Thm_ThreeSum_LightSourceStages_Procs_meets
import Theorems.Thm_ThreeSum_LightSourceStages_ZetaProcs_meets
import Definitions.Def_WeightedCache3SUM_Alias_b9dca0c4b48e489f
import Definitions.Def_WeightedCache3SUM_Alias_f29d07b5f5ce2e2c
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Definitions.Def_WeightedCache3SUM_Alias_037fdff845f4735d
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b
import Definitions.Def_WeightedCache3SUM_Alias_66dd70707634c020
import Definitions.Def_WeightedCache3SUM_Alias_cdc5e7727f35fd80
import Definitions.Def_WeightedCache3SUM_Alias_de9d37b5900d1a92
import Definitions.Def_WeightedCache3SUM_Alias_b5410f4bcc10d599
import Definitions.Def_WeightedCache3SUM_Alias_c0e528b1e0cee255
import Definitions.Def_WeightedCache3SUM_Alias_44f02ed11cdb23f7
import Definitions.Def_WeightedCache3SUM_Alias_d110f06b53aa1a96
import Definitions.Def_WeightedCache3SUM_Alias_197272b1cee37ac5

set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceRetainedHost
open Light BlockEncoding GlobalEncoding BlockIndex BlockCoefficientRows
open SubsetAddress LightSubsetAddress LightPascal LocalCoverBounds BlockSourceFlags
open BlockSourceEncoding LightBlockSourceBuild
set_option maxHeartbeats 4000000
set_option maxRecDepth 14000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightBlockSourceRetainedHost.Procs.meets_w3sum_ac885d1 {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    {pMain : ℕ} (C : Procs P pMain)
    {μ : ℕ → ℤ} {h J cut p NL NR occ maps candidates histL histR sourceHistL sourceHistR
      masks coeff0 coeff1 rawLeft rawRight flags baseL baseR maskBase bitBase rowOut work : ℕ}
    {shift : ℤ} (B : Finset β) (b : β → ℤ) (A : Finset γ) (a : γ → ℤ)
    (q : GlobalOutput h J) (vL vR : ℕ → ℤ) (eL : Fin NL ≃ B) (eR : Fin NR ≃ A)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*(512*h)+9 ≤ lim.depth)
    (hcut : cut ≤ J*(512*h))
    (hocc : occ+J ≤ masks) (hmaps : maps+2*(512*h)*scheduleSize h ≤ masks)
    (hcandidates : candidates+scheduleSize h ≤ masks)
    (hleft : histL+LightLocalCoverSchedule.rows h*localPrime h ≤ masks)
    (hright : histR+LightLocalCoverSchedule.rows h*localPrime h ≤ masks)
    (hsourceHistL : sourceHistL+modulus h J ≤ masks)
    (hsourceHistR : sourceHistR+modulus h J ≤ masks)
    (hmasks : masks+downsetCap (J*(512*h)) cut ≤ coeff0)
    (hc0 : coeff0+J*(512*h) ≤ coeff1) (hc1 : coeff1+J*(512*h) ≤ rawLeft)
    (hrawLeft : rawLeft+downsetCap (J*(512*h)) cut ≤ rawRight)
    (hrawRight : rawRight+downsetCap (J*(512*h)) cut ≤ flags)
    (hflags : flags+2*downsetCap (J*(512*h)) cut+2 ≤ baseL)
    (hbaseL : baseL+(J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤ baseR)
    (hbaseR : baseR+(J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤ maskBase)
    (hmaskBase : maskBase+downsetCap (J*(512*h)) cut ≤ bitBase)
    (hbits : bitBase+J*(512*h) ≤ rowOut) (hrowOut : rowOut+2 ≤ work)
    (hspace : space work h J ≤ lim.space)
    (hword : (word NL NR h J : ℤ) ≤ lim.word)
    (hinputL : ∀ i : Fin NL, vL i.val = b (eL i))
    (hinputR : ∀ i : Fin NR, vR i.val = a (eR i))
    (hhistReadL : ∀ r < modulus h J,
      μ (sourceHistL+r) = (LightBlockSourceRetainedStages.histogram p (modulus h J) 0 vL NL r : ℤ))
    (hhistReadR : ∀ r < modulus h J,
      μ (sourceHistR+r) = (LightBlockSourceRetainedStages.histogram p (modulus h J) shift vR NR r : ℤ))
    (hoccRead : ∀ j < J, μ (occ+j) = (occurrenceIndices (outputOccurrences q) j : ℤ))
    (hcover : BlockSourceCoverInput.Input μ h maps candidates histL histR) :
    Meets lim P pMain d
      [J,512*h,h,localPrime h,localBucketCap h,cut,modulus h J,occ,maps,candidates,
        histL,histR,sourceHistL,sourceHistR,masks,coeff0,coeff1,rawLeft,rawRight,flags,
        baseL,baseR,maskBase,bitBase,rowOut,work]
      μ (time h J cut) (fun _ ν =>
        LightZetaStages.StoredThrough ν baseL cut (BlockIndexedQuery.leftSource (p : ℤ) B b q) (J*(512*h)) ∧
        LightZetaStages.StoredThrough ν baseR cut (BlockIndexedQuery.rightSource (p : ℤ) shift A a q) (J*(512*h)) ∧
        Kept μ ν masks) := by sorry
