-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearSourceWords_meets
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearSourceWords.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:36:15.416445+00:00
-- url     : https://prove2.me/theorems/7a589d9a-ab05-4439-bcb5-3db036eebc4e
-- title:
--   meets
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/NearSourceWords.lean#L23-L134
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/NearSourceWords.lean#L23-L134

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearSource
import Definitions.Def_Submission_ThreeSum_LightTernaryProduct
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearSourceWords
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Theorems.Thm_ThreeSum_LightTernaryDivide_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerMemo_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerRow_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerScan_meets
import Theorems.Thm_ThreeSum_LightTernaryPass_meets
import Theorems.Thm_ThreeSum_LightTernaryProduct_meets
import Theorems.Thm_ThreeSum_LightTernaryRankTable_meets
import Theorems.Thm_ThreeSum_LightTernaryRank_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCost_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedEulerMetadata_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearSource_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedPredecessorTable_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedPredecessor_meets

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearSourceWords
open Light ThreeSum.LightSubsetAddress
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.WeightedBankEnumeration (cacheCost)
open ThreeSum.TernaryCodeSemantics ThreeSum.WeightedPhysicalEuler
set_option maxHeartbeats 5000000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program}

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearSourceWords.meets {pMain pRanks pMetadata pMemo pColumn pCell pDigit pZero pErase pRank pCost pSearch
    pScan pFill pRow pSum pDivide pNaturalDivide N a rows powers bank nb bv L T activeBase ws rankBase
    vals h pcount fr U V d : ℕ}
    (hmain : P[pMain]?=some (LightWeightedNearSource.body pRanks pMetadata pMemo))
    (hranks : P[pRanks]?=some (LightTernaryRankTable.body pRank))
    (hmetadata : P[pMetadata]?=some (LightWeightedEulerMetadata.body pColumn))
    (hmemo : P[pMemo]?=some (LightTernaryEulerMemo.body pScan))
    (hcolumn : P[pColumn]?=some (LightWeightedPredecessorTable.body pCell pDigit))
    (hcell : P[pCell]?=some (LightWeightedPredecessor.body pDigit pZero pErase pCost pSearch))
    (hdigit : P[pDigit]?=some (LightTernaryCodes.digitBody pErase))
    (hzero : P[pZero]?=some (LightTernaryCodes.zeroBody pErase))
    (herase : P[pErase]?=some (LightMaskErase.body pErase))
    (hrank : P[pRank]?=some (LightTernaryRank.body pDigit))
    (hcostProg : P[pCost]?=some (LightWeightedCost.body pDigit))
    (hsearch : P[pSearch]?=some (LightBandLookup.searchBody pSearch))
    (hscan : P[pScan]?=some (LightTernaryEulerScan.body pFill))
    (hfill : P[pFill]?=some (LightTernaryEulerRow.fillBody pRow))
    (hrow : P[pRow]?=some (LightTernaryEulerRow.body pSum pDivide))
    (hsum : P[pSum]?=some LightTernaryWeightedSum.body)
    (hdivide : P[pDivide]?=some (LightTernaryDivide.body pNaturalDivide))
    (hnatural : P[pNaturalDivide]?=some LightOutputDecodeDivide.body)
    (μ : ℕ → ℤ) (Q : TritWord N) (bankWords nearWords : ℕ → TritWord N)
    (source : TritWord N → ℤ) (homogeneous : ∀ A, source A≠0 → rank A=h)
    (F : ∀ current, h<current → current≤2*N → Light.Emod.Pre lim (current-h) V fr)
    (hw : (lim.space : ℤ)≤lim.word)
    (ha : a+rows≤ws) (hb : bank+nb≤ws) (hp : powers+(2*N+1)≤ws)
    (hactiveSpace : activeBase+N≤ws) (hbankVals : bv+nb≤ws)
    (hmetadataRanks : ws+2*N*rows+N≤rankBase)
    (hrankVals : rankBase+rows≤vals) (hvals : vals+rows≤fr) (hfr : fr≤lim.space)
    (hcount : vals+rows≤pcount) (hspace : pcount≤lim.space)
    (hword : ((nb+rows+2^(2*N+1)+2740*N+3000 : ℕ) : ℤ)≤lim.word)
    (hcontrols : ((T+N+32 : ℕ) : ℤ)≤lim.word)
    (hmemoWord : ((N+rows+2*N+h+20 : ℕ) : ℤ)≤lim.word)
    (hread : ∀ j<rows, μ (a+j)=(address (nearWords j) : ℤ))
    (hbankRead : ∀ j<nb, μ (bank+j)=(address (bankWords j) : ℤ))
    (hactiveRead : ∀ i<N, μ (activeBase+i)=1)
    (hbankSorted : ∀ j k, j<k → k<nb → address (bankWords j)<address (bankWords k))
    (hnearSorted : ∀ j k, j<k → k<rows → address (nearWords j)<address (nearWords k))
    (hpowers : Powers μ powers (2*N))
    (hL : L≤2*N) (hnb : nb<2^L) (hnn : rows<2^L) (hnbpos : 0<nb)
    (hbankPresent : ∀ W, cacheCost W≤T → ∃ j<nb, bankWords j=W)
    (hnearPresent : ∀ W, Below W Q → T<cacheCost W → ∃ j<rows, nearWords j=W)
    (hnearRows : ∀ j<rows, Below (nearWords j) Q ∧ T<cacheCost (nearWords j))
    (hT : h≤2*N) (hh : 2740*h≤2*T)
    (hbankValues : ∀ j<nb, μ (bv+j)=binomialZeta source (bankWords j))
    (hvalue : ∀ R, |binomialZeta source R|≤U)
    (hV : 2*(N+1)*U≤V) (hd : d+2*N+7≤lim.depth) :
    Meets lim P pMain d [N,a,rows,powers,bank,nb,bv,L,T,activeBase,ws,rankBase,vals,h,2*N,pcount,fr]
      μ (LightWeightedNearSource.time N L rows (2*N-h) V)
      (fun r ν => r=0 ∧ Kept μ ν ws ∧ ∀ j<rows, ν (vals+j)=binomialZeta source (nearWords j)) := by sorry
