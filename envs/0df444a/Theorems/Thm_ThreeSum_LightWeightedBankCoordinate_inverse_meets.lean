-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedBankCoordinate_inverse_meets
-- name    : ThreeSum.LightWeightedBankCoordinate.inverse_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:28:50.81552+00:00
-- url     : https://prove2.me/theorems/cf1d2806-c1c5-4275-b42a-c2e16bb01be6
-- title:
--   Light Weighted Bank Coordinate: inverse meets
-- statement:
--   The Light Weighted Bank Coordinate construction uses the inverse meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankCoordinate.lean#L101-L176
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankCoordinate.lean#L101-L176

import Definitions.Def_Submission_Weighted_BankStageModel
import Definitions.Def_Submission_Weighted_BankCoordinate
import Theorems.Thm_ThreeSum_LightTernaryCell_inverse_meets
import Theorems.Thm_ThreeSum_LightTernaryLookup_inverse_meets
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedBankCoordinate
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryQuery
set_option maxHeartbeats 5000000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightWeightedBankCoordinate.inverse_meets {N T n pMain pMeta pZero pDigit pErase pPass pCell pSearch pValue
    a powers L keyBase src dst d U : ℕ}
    (hmain : P[pMain]?=some (body pMeta pPass))
    (hmetaProg : P[pMeta]?=some (LightTernaryMetadata.body pZero pDigit pErase))
    (hzero : P[pZero]?=some (LightTernaryCodes.zeroBody pErase))
    (hdigit : P[pDigit]?=some (LightTernaryCodes.digitBody pErase))
    (herase : P[pErase]?=some (LightMaskErase.body pErase))
    (hpass : P[pPass]?=some (LightTernaryInversePass.body pCell))
    (hcell : P[pCell]?=some (LightTernaryLookup.body pSearch pValue))
    (hsearch : P[pSearch]?=some (LightBandLookup.searchBody pSearch))
    (hvalue : P[pValue]?=some LightTernaryCell.inverseBody)
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
      (fun _ μ' => (∀ j<n, μ' (dst+j)=coordinateInverse i F (E.word j)) ∧ Preserved μ μ' keyBase n dst) := by sorry
