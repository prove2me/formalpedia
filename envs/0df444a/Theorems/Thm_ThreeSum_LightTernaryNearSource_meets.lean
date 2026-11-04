-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryNearSource_meets
-- name    : ThreeSum.LightTernaryNearSource.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:48:57.232476+00:00
-- url     : https://prove2.me/theorems/13b5f896-babd-43d6-bbb7-ba2891fd4e8e
-- title:
--   Light Ternary Near Source: meets
-- statement:
--   The Light Ternary Near Source construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryNearSource.lean#L31-L141
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryNearSource.lean#L31-L141

import Definitions.Def_Submission_ThreeSum_TernaryPhysicalEuler
import Definitions.Def_Submission_ThreeSum_LightTernaryNearSource
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Theorems.Thm_ThreeSum_LightTernaryDivide_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerMemo_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerMetadata_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerRow_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerScan_meets
import Theorems.Thm_ThreeSum_LightTernaryPass_meets
import Theorems.Thm_ThreeSum_LightTernaryPredecessorTable_meets
import Theorems.Thm_ThreeSum_LightTernaryPredecessor_meets
import Theorems.Thm_ThreeSum_LightTernaryRankTable_meets
import Theorems.Thm_ThreeSum_LightTernaryRank_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryNearSource
open Light ThreeSum.LightSubsetAddress
open ThreeSum.LightTernaryEulerMetadata
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryNearSource.meets {pMain pRanks pMetadata pMemo pColumn pCell pDigit pZero pErase pRank pSearch
    pScan pFill pRow pSum pDivide pNaturalDivide N a rows powers bank nb bv L T activeBase ws rankBase
    vals h maxRank pcount fr U V d : ℕ}
    (hmain : P[pMain]?=some (body pRanks pMetadata pMemo))
    (hranks : P[pRanks]?=some (LightTernaryRankTable.body pRank))
    (hmetadata : P[pMetadata]?=some (LightTernaryEulerMetadata.body pColumn))
    (hmemo : P[pMemo]?=some (LightTernaryEulerMemo.body pScan))
    (hcolumn : P[pColumn]?=some (LightTernaryPredecessorTable.body pCell pDigit))
    (hcell : P[pCell]?=some (LightTernaryPredecessor.body pDigit pZero pErase pRank pSearch))
    (hdigit : P[pDigit]?=some (LightTernaryCodes.digitBody pErase))
    (hzero : P[pZero]?=some (LightTernaryCodes.zeroBody pErase))
    (herase : P[pErase]?=some (LightMaskErase.body pErase))
    (hrank : P[pRank]?=some (LightTernaryRank.body pDigit))
    (hsearch : P[pSearch]?=some (LightBandLookup.searchBody pSearch))
    (hscan : P[pScan]?=some (LightTernaryEulerScan.body pFill))
    (hfill : P[pFill]?=some (LightTernaryEulerRow.fillBody pRow))
    (hrow : P[pRow]?=some (LightTernaryEulerRow.body pSum pDivide))
    (hsum : P[pSum]?=some LightTernaryWeightedSum.body)
    (hdivide : P[pDivide]?=some (LightTernaryDivide.body pNaturalDivide))
    (hnatural : P[pNaturalDivide]?=some LightOutputDecodeDivide.body)
    (μ : ℕ → ℤ) (codes bankCodes active : ℕ → ℕ) (bi ni : ℕ → ℕ → ℕ)
    (g f : ℕ → ℤ)
    (F : ∀ current, T<current → current≤maxRank → Light.Emod.Pre lim (current-h) V fr)
    (hw : (lim.space : ℤ)≤lim.word)
    (ha : a+rows≤ws) (hb : bank+nb≤ws) (hp : powers+(2*N+1)≤ws)
    (hactiveSpace : activeBase+N≤ws) (hbankVals : bv+nb≤ws)
    (hmetadataRanks : ws+2*N*rows+N≤rankBase)
    (hrankVals : rankBase+rows≤vals) (hvals : vals+rows≤fr) (hfr : fr≤lim.space)
    (hspace : pcount≤lim.space)
    (hword : ((nb+rows+2^(2*N+1)+2*N+32 : ℕ) : ℤ)≤lim.word)
    (hcontrols : ((T+N+32 : ℕ) : ℤ)≤lim.word)
    (hmemoWord : ((N+rows+maxRank+h+20 : ℕ) : ℤ)≤lim.word)
    (hread : ∀ j<rows, μ (a+j)=(codes j : ℤ))
    (hbankRead : ∀ j<nb, μ (bank+j)=(bankCodes j : ℤ))
    (hactiveRead : ∀ i<N, μ (activeBase+i)=(active i : ℤ))
    (hbankSorted : ∀ j k, j<k → k<nb → bankCodes j<bankCodes k)
    (hnearSorted : ∀ j k, j<k → k<rows → codes j<codes k)
    (hpowers : Powers μ powers (2*N)) (hcodes : ∀ j<rows, codes j<2^(2*N))
    (hL : L≤2*N) (hnb : nb<2^L) (hnn : rows<2^L) (hnbpos : 0<nb)
    (hactive : ∀ i<N, active i≤1)
    (hbi : ∀ i<N, ∀ j<rows, active i≠0 → LightTernaryPredecessor.digit N (lowAt N i) (highAt N i) (codes j)≠0 →
      LightTernaryPredecessor.predRank N (lowAt N i) (highAt N i) (codes j)≤T →
      bi i j<nb ∧ bankCodes (bi i j)=LightTernaryPredecessor.code N (lowAt N i) (highAt N i) (codes j))
    (hni : ∀ i<N, ∀ j<rows, active i≠0 → LightTernaryPredecessor.digit N (lowAt N i) (highAt N i) (codes j)≠0 →
      T<LightTernaryPredecessor.predRank N (lowAt N i) (highAt N i) (codes j) →
      ni i j<rows ∧ codes (ni i j)=LightTernaryPredecessor.code N (lowAt N i) (highAt N i) (codes j))
    (hT : T≤maxRank) (hh : h≤T)
    (hrankRange : ∀ j<rows, T<ranks N codes j ∧ ranks N codes j≤maxRank)
    (hrange : ∀ j<rows, ∀ i<N, keys N rows T bv vals codes active bi ni j i<pcount ∧
      keys N rows T bv vals codes active bi ni j i<fr)
    (hbank : ∀ j<rows, ∀ i<N, keys N rows T bv vals codes active bi ni j i<vals →
      keys N rows T bv vals codes active bi ni j i<ws ∧
      μ (keys N rows T bv vals codes active bi ni j i)=g (keys N rows T bv vals codes active bi ni j i))
    (hmemoval : ∀ j<rows, g (vals+j)=f j)
    (hweight : ∀ j<rows, ∀ i<N, weights N codes active j i≤2)
    (hvalue : ∀ j<rows, ∀ i<N, |g (keys N rows T bv vals codes active bi ni j i)|≤U)
    (hpre : ∀ j<rows, ∀ i<N, keys N rows T bv vals codes active bi ni j i<vals ∨
      ∃ k<rows, keys N rows T bv vals codes active bi ni j i=vals+k ∧ ranks N codes k<ranks N codes j)
    (hEuler : ∀ j<rows, LightTernaryWeightedSum.sum (weights N codes active j)
      (keys N rows T bv vals codes active bi ni j) g N=(ranks N codes j-h : ℕ)*f j)
    (hV : 2*(N+1)*U≤V) (hd : d+2*N+7≤lim.depth) :
    Meets lim P pMain d [N,a,rows,powers,bank,nb,bv,L,T,activeBase,ws,rankBase,vals,h,maxRank,pcount,fr]
      μ (time N L rows (maxRank-T) V)
      (fun r ν => r=0 ∧ Kept μ ν ws ∧ ∀ j<rows, ν (vals+j)=f j) := by sorry
