-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryBankStages_inverse_meets
-- name    : ThreeSum.LightTernaryBankStages.inverse_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:57:06.62486+00:00
-- url     : https://prove2.me/theorems/2d252a12-9eaf-4487-995b-5826c6b96004
-- title:
--   Light Ternary Bank Stages: inverse meets
-- statement:
--   The Light Ternary Bank Stages construction uses the inverse meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryBankStages.lean#L69-L106
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryBankStages.lean#L69-L106

import Definitions.Def_Submission_ThreeSum_LightTernaryBankSweep
import Definitions.Def_Submission_ThreeSum_LightTernaryBankStages
import Theorems.Thm_ThreeSum_LightTernaryBankCoordinate_inverse_meets
import Theorems.Thm_ThreeSum_LightTernaryCell_inverse_meets
import Theorems.Thm_ThreeSum_LightTernaryLookup_inverse_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryBankStages
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryQuery ThreeSum.TernaryFrozenQueryStages
open ThreeSum.LightTernaryBankSweep
set_option maxHeartbeats 5000000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryBankStages.inverse_meets {N T n pMain pCoord pMeta pZero pDigit pErase pPass pCell pSearch pValue
    a powers L keyBase base d V : ℕ}
    (hmain : P[pMain]?=some (LightTernaryBankSweep.body pCoord))
    (hcoord : P[pCoord]?=some (LightTernaryBankCoordinate.body pMeta pPass))
    (hmetaProg : P[pMeta]?=some (LightTernaryMetadata.body pZero pDigit pErase))
    (hzero : P[pZero]?=some (LightTernaryCodes.zeroBody pErase))
    (hdigit : P[pDigit]?=some (LightTernaryCodes.digitBody pErase))
    (herase : P[pErase]?=some (LightMaskErase.body pErase))
    (hpass : P[pPass]?=some (LightTernaryInversePass.body pCell))
    (hcell : P[pCell]?=some (LightTernaryLookup.body pSearch pValue))
    (hsearch : P[pSearch]?=some (LightBandLookup.searchBody pSearch))
    (hvalue : P[pValue]?=some LightTernaryCell.inverseBody)
    (E : Enumeration N T n) (H : TritWord N→ℤ) (μ : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word)
    (ha : a+n≤keyBase) (hmeta : keyBase+4*n≤powers)
    (hpows : powers+(2*N+1)≤base) (hspace : base+(N+1)*n≤lim.space)
    (hword : ((n+2^(2*N+1)+16 : ℕ) : ℤ)≤lim.word)
    (hNword : 2*(N : ℤ)+3≤lim.word)
    (hcodes : ∀ j<n, μ (a+j)=(address (E.word j) : ℤ))
    (hsource : ∀ j<n, μ (base+j)=H (E.word j))
    (hpowers : Powers μ powers (2*N))
    (hsorted : ∀ j k, j<k → k<n → address (E.word j)<address (E.word k))
    (hH : ∀ R, |H R|≤(V : ℤ)) (hvalword : 4*((4^N*V : ℕ) : ℤ)+3≤lim.word)
    (hL : L≤2*N) (hn : n<2^L) (hd : d+2*N+L+5≤lim.depth) :
    Meets lim P pMain d [N,a,n,powers,L,keyBase,base] μ (time N L n)
      (fun _ μ' => Stages E (fun s => stageValue s H) base N μ' ∧
        Preserved μ μ' keyBase n base N ∧ Powers μ' powers (2*N)) := by sorry
