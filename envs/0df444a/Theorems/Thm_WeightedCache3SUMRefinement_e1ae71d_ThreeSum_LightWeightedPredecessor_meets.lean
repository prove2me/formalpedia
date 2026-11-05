-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedPredecessor_meets
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPredecessor.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:18:29.034+00:00
-- url     : https://prove2.me/theorems/0e5a09b4-b9cc-494d-bb1c-54df7bfe4200
-- title:
--   meets
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Predecessor.lean#L99-L233
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Predecessor.lean#L99-L233

import Definitions.Def_Submission_ThreeSum_LightTernaryRankTable
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_LightCost
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Predecessor
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Theorems.Thm_ThreeSum_LightTernaryPass_meets
import Theorems.Thm_ThreeSum_LightTernaryRankTable_meets
import Theorems.Thm_ThreeSum_LightTernaryRank_meets
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCost_meets

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPredecessor
open Light ThreeSum.LightSubsetAddress ThreeSum.MaskErase
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryCodeSemantics
open ThreeSum.TernaryEuler
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPredecessor.meets {pMain pDigit pZero pErase pRank pSearch N low high m powers
    bank nb bankVals near nn nearVals L T active bi ni d : ℕ}
    (hmain : P[pMain]?=some (body pDigit pZero pErase pRank pSearch))
    (hdigit : P[pDigit]?=some (LightTernaryCodes.digitBody pErase))
    (hzero : P[pZero]?=some (LightTernaryCodes.zeroBody pErase))
    (herase : P[pErase]?=some (LightMaskErase.body pErase))
    (hrank : P[pRank]?=some (LightWeightedCost.body pDigit))
    (hsearch : P[pSearch]?=some (LightBandLookup.searchBody pSearch))
    (μ : ℕ → ℤ) (bankCodes nearCodes : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hbankSpace : bank+nb ≤ lim.space) (hnearSpace : near+nn ≤ lim.space)
    (hbankVals : bankVals+nb ≤ lim.space) (hnearVals : nearVals+nn ≤ lim.space)
    (hspace : powers+(2*N+1) ≤ lim.space)
    (hword : ((nb+nn+2^(2*N+1)+2740*N+3000 : ℕ) : ℤ) ≤ lim.word)
    (hcontrols : ((T+active+16 : ℕ) : ℤ) ≤ lim.word)
    (hbankRead : ∀ j<nb, μ (bank+j)=(bankCodes j : ℤ))
    (hnearRead : ∀ j<nn, μ (near+j)=(nearCodes j : ℤ))
    (hbankSorted : ∀ j k, j<k → k<nb → bankCodes j<bankCodes k)
    (hnearSorted : ∀ j k, j<k → k<nn → nearCodes j<nearCodes k)
    (hpowers : Powers μ powers (2*N)) (hm : m<2^(2*N))
    (hlow : low≤2*N) (hhigh : high≤2*N) (hL : L≤2*N)
    (hnb : nb<2^L) (hnn : nn<2^L) (hnbpos : 0<nb)
    (hbi : active≠0 → digit N low high m≠0 → predCost N low high m≤T →
      bi<nb ∧ bankCodes bi=code N low high m)
    (hni : active≠0 → digit N low high m≠0 → T<predCost N low high m →
      ni<nn ∧ nearCodes ni=code N low high m)
    (hd : d+2*N+3 ≤ lim.depth) :
    Meets lim P pMain d [N,low,high,m,powers,bank,nb,bankVals,near,nn,nearVals,L,T,active]
      μ (time N L)
      (fun r ν => r=(key N low high m T active bankVals nearVals bi ni : ℤ) ∧ ν=μ) := by sorry
