-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverCandidate_Procs_meets_w3sum_ac885d1
-- name    : ThreeSum.LightLocalCoverCandidate.Procs.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:56:56.622789+00:00
-- url     : https://prove2.me/theorems/63921cc5-342b-4b73-bd50-612c4160fd24
-- title:
--   Procs: meets
-- statement:
--   The Procs construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverCandidate.lean#L57-L200
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverCandidate.lean#L57-L200

import Definitions.Def_Submission_ThreeSum_LightWeightDecode
import Definitions.Def_Submission_ThreeSum_LightLocalCoverHashHistogram
import Definitions.Def_Submission_ThreeSum_LightLocalCoverRow
import Definitions.Def_Submission_ThreeSum_LightLocalCoverCandidate
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Theorems.Thm_ThreeSum_LightHashHistogram_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_da105011ac4dcdd4
import Definitions.Def_WeightedCache3SUM_Alias_a64b3be7ea8b7b19
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Definitions.Def_WeightedCache3SUM_Alias_9176929b72776235
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Definitions.Def_WeightedCache3SUM_Alias_66dd70707634c020
import Definitions.Def_WeightedCache3SUM_Alias_cdc5e7727f35fd80
import Definitions.Def_WeightedCache3SUM_Alias_de9d37b5900d1a92
import Definitions.Def_WeightedCache3SUM_Alias_b5410f4bcc10d599

set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverCandidate
open Light
set_option maxHeartbeats 2000000
set_option maxRecDepth 6000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightLocalCoverCandidate.Procs.meets_w3sum_ac885d1 {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {L n p cap index masks bitPtr coef raw0 raw1 hist0 hist1 dst work : ℕ}
    (mask w0 w1 : ℕ → ℕ) (bits : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+L+4 ≤ lim.depth) (hp : 0 < p) (hn : 0 < n)
    (hspace : space work L n p ≤ lim.space)
    (hmasks : masks+n ≤ coef) (hbits : bitPtr+n*L ≤ coef) (hcoef : coef+2*L ≤ raw0)
    (hraw0 : raw0+2*n ≤ raw1) (hraw1 : raw1+2*n ≤ hist0)
    (hhist0 : hist0+p ≤ hist1) (hhist1 : hist1+p ≤ dst) (hdst : dst+p*p ≤ work)
    (hword : (word L n p cap index : ℤ) ≤ lim.word)
    (hmaskRead : ∀ i < n, μ (masks+i) = (mask i : ℤ))
    (hmaskLt : ∀ i < n, mask i < 2^L)
    (hbitsRead : ∀ i < n, ∀ j < L, μ (bitPtr+i*L+j) = (bits i j : ℤ))
    (hbitsValue : ∀ i < n, ∀ j < L, bits i j ≤ 1)
    (hw0 : ∀ i < L, w0 i = WeightEnumeration.digit p (2*L) index (2*i))
    (hw1 : ∀ i < L, w1 i = WeightEnumeration.digit p (2*L) index (2*i+1)) :
    Meets lim P pMain d [L,p,index,n,cap,masks,bitPtr,coef,raw0,raw1,hist0,hist1,dst,work] μ
      (time L n p index)
      (fun _ μ' => LightWeightDecode.Rows μ' coef L p index ∧
        (∀ r < p,
          μ' (hist0+r) = (LightHistogram.count (LightHashHistogram.code L p mask w0 w1) r n : ℤ) ∧
          μ' (hist1+r) = (LightHistogram.count (LightHashHistogram.code L p mask w1 w0) r n : ℤ)) ∧
        (∀ r < p*p, μ' (dst+r) = (entry L n p cap mask bits w0 w1 r : ℤ)) ∧
        Preserved μ μ' work coef raw0 raw1 hist0 hist1 dst L n p) := by sorry
