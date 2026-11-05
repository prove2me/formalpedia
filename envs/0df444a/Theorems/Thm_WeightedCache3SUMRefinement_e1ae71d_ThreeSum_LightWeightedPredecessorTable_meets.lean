-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedPredecessorTable_meets
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPredecessorTable.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:20:56.952481+00:00
-- url     : https://prove2.me/theorems/366fdb71-8645-4881-9893-b6f9e1e764b8
-- title:
--   meets
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/PredecessorTable.lean#L91-L220
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/PredecessorTable.lean#L91-L220

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Predecessor
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_PredecessorTable
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Theorems.Thm_ThreeSum_LightTernaryPass_meets
import Theorems.Thm_ThreeSum_LightTernaryRankTable_meets
import Theorems.Thm_ThreeSum_LightTernaryRank_meets
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCost_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedPredecessor_meets

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPredecessorTable
open Light ThreeSum.LightSubsetAddress ThreeSum.LightWeightedPredecessor
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPredecessorTable.meets {pMain pCell pDigit pZero pErase pRank pSearch N low high a n powers
    bank nb bv near nn nv L T active dst stride d : ℕ}
    (hmain : P[pMain]?=some (body pCell pDigit))
    (hcell : P[pCell]?=some (LightWeightedPredecessor.body pDigit pZero pErase pRank pSearch))
    (hdigit : P[pDigit]?=some (LightTernaryCodes.digitBody pErase))
    (hzero : P[pZero]?=some (LightTernaryCodes.zeroBody pErase))
    (herase : P[pErase]?=some (LightMaskErase.body pErase))
    (hrank : P[pRank]?=some (LightWeightedCost.body pDigit))
    (hsearch : P[pSearch]?=some (LightBandLookup.searchBody pSearch))
    (μ : ℕ → ℤ) (codes bankCodes nearCodes bi ni : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+n≤dst) (hbankSpace : bank+nb≤dst) (hnearSpace : near+nn≤dst)
    (hspace : powers+(2*N+1)≤dst) (hdst : dst+2*stride*n≤lim.space)
    (hbankVals : bv+nb≤lim.space) (hnearVals : nv+nn≤lim.space)
    (hword : ((nb+nn+2^(2*N+1)+2740*N+3000 : ℕ) : ℤ)≤lim.word)
    (hcontrols : ((T+active+stride+16 : ℕ) : ℤ)≤lim.word)
    (hread : ∀ j<n, μ (a+j)=(codes j : ℤ))
    (hbankRead : ∀ j<nb, μ (bank+j)=(bankCodes j : ℤ))
    (hnearRead : ∀ j<nn, μ (near+j)=(nearCodes j : ℤ))
    (hbankSorted : ∀ j k, j<k → k<nb → bankCodes j<bankCodes k)
    (hnearSorted : ∀ j k, j<k → k<nn → nearCodes j<nearCodes k)
    (hpowers : Powers μ powers (2*N)) (hcodes : ∀ j<n, codes j<2^(2*N))
    (hlow : low≤2*N) (hhigh : high≤2*N) (hL : L≤2*N)
    (hnb : nb<2^L) (hnn : nn<2^L) (hnbpos : 0<nb)
    (hactive : active≤1) (hstride : 0<stride)
    (hbi : ∀ j<n, active≠0 → digit N low high (codes j)≠0 →
      predCost N low high (codes j)≤T → bi j<nb ∧ bankCodes (bi j)=code N low high (codes j))
    (hni : ∀ j<n, active≠0 → digit N low high (codes j)≠0 →
      T<predCost N low high (codes j) → ni j<nn ∧ nearCodes (ni j)=code N low high (codes j))
    (hd : d+2*N+4≤lim.depth) :
    Meets lim P pMain d [N,low,high,a,n,powers,bank,nb,bv,near,nn,nv,L,T,active,dst,stride]
      μ (time N L n)
      (fun _ ν => (∀ j<n, RecordAt ν dst stride n j N low high (codes j) T active bv nv (bi j) (ni j)) ∧
        KeptApart μ ν dst stride n ∧ SameOutside μ ν dst (2*stride*n)) := by sorry
