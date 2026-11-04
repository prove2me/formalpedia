-- Prove2me | Theorems.Thm_ThreeSum_LightBandWeightedScoreCell_meets_w3sum_ac885d1
-- name    : ThreeSum.LightBandWeightedScoreCell.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:38:28.569892+00:00
-- url     : https://prove2.me/theorems/52b255b3-6c36-4e65-828c-1cf97a4ddfd5
-- title:
--   Light Band Weighted Score Cell: meets
-- statement:
--   The Light Band Weighted Score Cell construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandWeightedScoreCell.lean#L58-L148
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandWeightedScoreCell.lean#L58-L148

import Definitions.Def_Submission_ThreeSum_LightBandWeightedScoreSlice
import Definitions.Def_Submission_ThreeSum_BandCandidateRowsMemory
import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Definitions.Def_Submission_ThreeSum_LightBandWeightedScoreCell
import Theorems.Thm_Light_Ends_block
import Definitions.Def_WeightedCache3SUM_Alias_4c62aff33317338c
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_f2e191e7f7b92ebc
import Definitions.Def_WeightedCache3SUM_Alias_0f0d845b38fcc358
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Definitions.Def_WeightedCache3SUM_Alias_eb65baeba73fd57c
import Definitions.Def_WeightedCache3SUM_Alias_3b3552e2795ab46d
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_e1d95931a2ead3e4
import Theorems.Thm_ThreeSum_LightModuloCounts_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_03cdb09d18890d4e
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Theorems.Thm_ThreeSum_LightPrimeChain_Procs_meets
import Theorems.Thm_ThreeSum_LightPrimeMinimum_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Theorems.Thm_ThreeSum_LightScaleArray_meets
import Definitions.Def_WeightedCache3SUM_Alias_280261ae8ac7fab5
import Theorems.Thm_ThreeSum_ReportingHostRelocation_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandWeightedScoreCell
open Light BandCandidateRows BandWeightedScore
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g rec q aux s free maxMod U : ℕ}

theorem ThreeSum.LightBandWeightedScoreCell.meets_w3sum_ac885d1 {pMain pLength pScore : ℕ} (S : LightWeightedScore.Procs P pScore)
    (hmain : P[pMain]?=some (body pLength pScore))
    (hlength : P[pLength]?=some LightBandWeightedScoreSlice.body)
    (primes : ℕ → ℕ) (r : Record)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+Nat.clog 2 maxMod+5 ≤ lim.depth)
    (hg : 0 < g) (hq : 0 < q) (hqmax : q ≤ maxMod)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (hrec : rec+4 ≤ free) (haux : aux+s ≤ free)
    (hspace : LightWeightedScore.space free maxMod g U ≤ lim.space)
    (hword : (word maxMod nA nB nC g s U : ℤ) ≤ lim.word)
    (hrecord : Seg μ rec r.cells) (hflag : r.flag=0 ∨ r.flag=1)
    (hvalid : r.flag=1 → r.a*g ≤ nA ∧ r.b*g ≤ nB ∧ r.c*g ≤ nC)
    (hA : ∀ i < nA, |μ (a+i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b+i)| ≤ (U : ℤ))
    (hC : ∀ i < nC, |μ (c+i)| ≤ (U : ℤ))
    (hread : ∀ i < s, μ (aux+i)=(primes i : ℤ))
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i=primes j → i=j)
    (hproduct : ∀ i < s, q*primes i ≤ maxMod) :
    Meets lim P pMain d [a,b,c,nA,nB,nC,g,rec,q,aux,s,free] μ (time maxMod g s U)
      (fun result ν => result=(block primes s q nA nB nC g
        (fun i => μ (a+i)) (fun i => μ (b+i)) (fun i => μ (c+i)) r : ℤ) ∧ Kept μ ν free) := by sorry
