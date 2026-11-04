-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryEulerMetadata_meets
-- name    : ThreeSum.LightTernaryEulerMetadata.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:18:01.546832+00:00
-- url     : https://prove2.me/theorems/83b29c9f-030e-4747-9e9b-2551a9c8e31b
-- title:
--   Light Ternary Euler Metadata: meets
-- statement:
--   The Light Ternary Euler Metadata construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEulerMetadata.lean#L73-L173
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEulerMetadata.lean#L73-L173

import Definitions.Def_Submission_ThreeSum_LightTernaryPredecessorTable
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMetadata
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Theorems.Thm_ThreeSum_LightTernaryPass_meets
import Theorems.Thm_ThreeSum_LightTernaryPredecessorTable_meets
import Theorems.Thm_ThreeSum_LightTernaryPredecessor_meets
import Theorems.Thm_ThreeSum_LightTernaryRankTable_meets
import Theorems.Thm_ThreeSum_LightTernaryRank_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryEulerMetadata
open Light ThreeSum.LightSubsetAddress ThreeSum.LightTernaryPredecessor
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryEulerMetadata.meets {pMain pColumn pCell pDigit pZero pErase pRank pSearch N a rows powers
    bank nb bv near nn nv L T activeBase ws d : ℕ}
    (hmain : P[pMain]?=some (body pColumn))
    (hcolumn : P[pColumn]?=some (LightTernaryPredecessorTable.body pCell pDigit))
    (hcell : P[pCell]?=some (LightTernaryPredecessor.body pDigit pZero pErase pRank pSearch))
    (hdigit : P[pDigit]?=some (LightTernaryCodes.digitBody pErase))
    (hzero : P[pZero]?=some (LightTernaryCodes.zeroBody pErase))
    (herase : P[pErase]?=some (LightMaskErase.body pErase))
    (hrank : P[pRank]?=some (LightTernaryRank.body pDigit))
    (hsearch : P[pSearch]?=some (LightBandLookup.searchBody pSearch))
    (μ : ℕ → ℤ) (codes bankCodes nearCodes active : ℕ → ℕ) (bi ni : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ)≤lim.word)
    (ha : a+rows≤ws) (hbankSpace : bank+nb≤ws) (hnearSpace : near+nn≤ws)
    (hspace : powers+(2*N+1)≤ws) (hactiveSpace : activeBase+N≤ws)
    (hws : ws+2*N*rows+N≤lim.space)
    (hbankVals : bv+nb≤lim.space) (hnearVals : nv+nn≤lim.space)
    (hword : ((nb+nn+2^(2*N+1)+2*N+32 : ℕ) : ℤ)≤lim.word)
    (hcontrols : ((T+N+32 : ℕ) : ℤ)≤lim.word)
    (hread : ∀ j<rows, μ (a+j)=(codes j : ℤ))
    (hbankRead : ∀ j<nb, μ (bank+j)=(bankCodes j : ℤ))
    (hnearRead : ∀ j<nn, μ (near+j)=(nearCodes j : ℤ))
    (hactiveRead : ∀ i<N, μ (activeBase+i)=(active i : ℤ))
    (hbankSorted : ∀ j k, j<k → k<nb → bankCodes j<bankCodes k)
    (hnearSorted : ∀ j k, j<k → k<nn → nearCodes j<nearCodes k)
    (hpowers : Powers μ powers (2*N)) (hcodes : ∀ j<rows, codes j<2^(2*N))
    (hL : L≤2*N) (hnb : nb<2^L) (hnn : nn<2^L) (hnbpos : 0<nb)
    (hactive : ∀ i<N, active i≤1)
    (hbi : ∀ i<N, ∀ j<rows, active i≠0 → digit N (lowAt N i) (highAt N i) (codes j)≠0 →
      predRank N (lowAt N i) (highAt N i) (codes j)≤T →
      bi i j<nb ∧ bankCodes (bi i j)=code N (lowAt N i) (highAt N i) (codes j))
    (hni : ∀ i<N, ∀ j<rows, active i≠0 → digit N (lowAt N i) (highAt N i) (codes j)≠0 →
      T<predRank N (lowAt N i) (highAt N i) (codes j) →
      ni i j<nn ∧ nearCodes (ni i j)=code N (lowAt N i) (highAt N i) (codes j))
    (hd : d+2*N+5≤lim.depth) :
    Meets lim P pMain d [N,a,rows,powers,bank,nb,bv,near,nn,nv,L,T,activeBase,ws]
      μ (time N L rows)
      (fun _ ν => (∀ i<N, ∀ j<rows, RecordAt ν N rows ws i j (codes j) T (active i) bv nv (bi i j) (ni i j)) ∧
        SameOutside μ ν ws (2*N*rows)) := by sorry
