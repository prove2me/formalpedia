-- Prove2me | Theorems.Thm_ThreeSum_LightSourceBandBanks_afterCount_ends_w3sum_ac885d1
-- name    : ThreeSum.LightSourceBandBanks.afterCount_ends_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:12:23.293747+00:00
-- url     : https://prove2.me/theorems/ef429609-01e3-494d-b227-7674d1dee507
-- title:
--   Light Source Band Banks: after Count ends
-- statement:
--   The Light Source Band Banks construction uses the after Count ends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBandBanks.lean#L70-L169
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBandBanks.lean#L70-L169

import Definitions.Def_Submission_ThreeSum_LightSourceBandBankBatch
import Definitions.Def_Submission_ThreeSum_SourceBandBankData
import Definitions.Def_Submission_ThreeSum_LightSourceOccurrenceArray
import Definitions.Def_Submission_ThreeSum_LightSourceBandBanks
import Theorems.Thm_Light_Ends_next
import Theorems.Thm_ThreeSum_Karatsuba_CoeffBound_mem

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBandBanks
open Light GlobalEncoding BlockEncoding BlockCoefficientRows BlockSourceEncoding
open LocalCoverBounds SubsetAddress BlockSourceOccurrenceOrder SourceBandBankLayout SourceBandBankData
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceBandBanks.afterCount_ends_w3sum_ac885d1 {pRows pDigits pDivide pBanks : ℕ}
    (hrows : P[pRows]?=some (LightSourceOccurrenceArray.body pDigits))
    (hdigits : P[pDigits]?=some (LightOutputDecodeDigits.body pDivide))
    (hdivide : P[pDivide]?=some LightOutputDecodeDivide.body)
    (C : LightSourceBandBankBatch.Procs P pBanks)
    {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {pair NL NR g p h J cut occ maps candidates histL histR base K : ℕ}
    {shift : ℤ} (H : SourceBandPairData.Stored μ fL fR pair NL NR g p (modulus h J) shift)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*(512*h)+14 ≤ lim.depth)
    (hg : 0 < g) (hcut : cut ≤ J*(512*h)) (hK : K=SourceBandPairSlices.count NL NR g)
    (hpair : SourceBandPairData.next pair NL NR g (modulus h J) ≤ occ)
    (hocc : occ+LightBlockSourceCatalog.count h J*J ≤ base)
    (hmaps : maps+2*(512*h)*scheduleSize h ≤ occ)
    (hcandidates : candidates+scheduleSize h ≤ occ)
    (hleft : histL+LightLocalCoverSchedule.rows h*localPrime h ≤ occ)
    (hright : histR+LightLocalCoverSchedule.rows h*localPrime h ≤ occ)
    (hspace : space base NL NR g h J cut ≤ lim.space)
    (hword : (word NL NR h J : ℤ) ≤ lim.word)
    (hcover : BlockSourceCoverInput.Input μ h maps candidates histL histR) :
    Ends lim P d (afterCountBody pRows pBanks)
      ⟨frame [J,512*h,h,localPrime h,localBucketCap h,cut,modulus h J,occ,maps,candidates,histL,histR,
        pair,base,downsetCap (J*(512*h)) cut,LightBlockSourceCatalog.count h J,scheduleSize h,span h J cut,K],μ⟩
      (afterTime NL NR g h J cut) (fun σ =>
        σ.loc 0=(finish base NL NR g h J cut : ℤ) ∧
        Stored σ.mem fL fR base NL NR g h J cut occ (p : ℤ) shift ∧ Kept μ σ.mem occ) := by sorry
