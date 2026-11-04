-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryBankCoordinate_zeta_meets
-- name    : ThreeSum.LightTernaryBankCoordinate.zeta_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:29:15.016825+00:00
-- url     : https://prove2.me/theorems/2bab5cd2-8a54-40ef-885e-a3cc995bd51e
-- title:
--   Light Ternary Bank Coordinate: zeta meets
-- statement:
--   The Light Ternary Bank Coordinate construction uses the zeta meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryBankCoordinate.lean#L19-L94
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryBankCoordinate.lean#L19-L94

import Definitions.Def_Submission_ThreeSum_TernaryBankStageModel
import Definitions.Def_Submission_ThreeSum_LightTernaryBankCoordinate
import Theorems.Thm_ThreeSum_LightTernaryCell_zeta_meets
import Theorems.Thm_ThreeSum_LightTernaryLookup_zeta_meets
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryBankCoordinate
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryQuery
set_option maxHeartbeats 5000000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryBankCoordinate.zeta_meets {N T n pMain pMeta pZero pDigit pErase pPass pCell pSearch pValue
    a powers L keyBase src dst d U : ℕ}
    (hmain : P[pMain]?=some (body pMeta pPass))
    (hmetaProg : P[pMeta]?=some (LightTernaryMetadata.body pZero pDigit pErase))
    (hzero : P[pZero]?=some (LightTernaryCodes.zeroBody pErase))
    (hdigit : P[pDigit]?=some (LightTernaryCodes.digitBody pErase))
    (herase : P[pErase]?=some (LightMaskErase.body pErase))
    (hpass : P[pPass]?=some (LightTernaryPass.body pCell))
    (hcell : P[pCell]?=some (LightTernaryLookup.body pSearch pValue))
    (hsearch : P[pSearch]?=some (LightBandLookup.searchBody pSearch))
    (hvalue : P[pValue]?=some LightTernaryCell.zetaBody)
    (E : Enumeration N T n) (i : Fin N) (F : TritWord N→ℤ) (μ : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word)
    (ha : a+n≤keyBase) (hmeta : keyBase+4*n≤powers)
    (hpows : powers+(2*N+1)≤src) (hsrc : src+n≤dst) (hdst : dst+n≤lim.space)
    (hword : ((n+2^(2*N+1)+16 : ℕ) : ℤ)≤lim.word)
    (hNword : 2*(N : ℤ)+3≤lim.word)
    (hcodes : ∀ j<n, μ (a+j)=(address (E.word j) : ℤ))
    (hsource : ∀ j<n, μ (src+j)=F (E.word j))
    (hpowers : Powers μ powers (2*N))
    (hsorted : ∀ j k, j<k → k<n → address (E.word j)<address (E.word k))
    (hF : ∀ j<n, |F (E.word j)|≤(U : ℤ)) (hvalword : 4*(U : ℤ)+3≤lim.word)
    (hL : L≤2*N) (hn : n<2^L) (hd : d+2*N+L+4≤lim.depth) :
    Meets lim P pMain d [N,low i,high i,a,n,powers,L,keyBase,src,dst] μ (time N L n)
      (fun _ μ' => (∀ j<n, μ' (dst+j)=coordinateZeta i F (E.word j)) ∧ Preserved μ μ' keyBase n dst) := by sorry
