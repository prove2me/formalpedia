-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryBankSweep_meets_core
-- name    : ThreeSum.LightTernaryBankSweep.meets_core
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:58:33.520752+00:00
-- url     : https://prove2.me/theorems/2fe40038-ca84-449e-8e20-0b7e575b4970
-- title:
--   Light Ternary Bank Sweep: meets core
-- statement:
--   Generic loop rule; its coordinate premise is instantiated by the real
--   metadata/pass routine in the concrete zeta and inverse sweep theorems.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryBankSweep.lean#L33-L132
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryBankSweep.lean#L33-L132

import Definitions.Def_Submission_ThreeSum_LightTernaryBankCoordinate
import Definitions.Def_Submission_ThreeSum_LightTernaryBankSweep
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryBankSweep
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
set_option maxHeartbeats 5000000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryBankSweep.meets_core {N T n pMain pCoord a powers L keyBase base d : ℕ}
    (hmain : P[pMain]?=some (body pCoord))
    (E : Enumeration N T n) (φ : ℕ→TritWord N→ℤ) (μ : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word)
    (ha : a+n≤keyBase) (hmeta : keyBase+4*n≤powers)
    (hpows : powers+(2*N+1)≤base) (hspace : base+(N+1)*n≤lim.space)
    (hNword : 2*(N : ℤ)+3≤lim.word) (hL : L≤2*N)
    (hcodes : ∀ j<n, μ (a+j)=(address (E.word j) : ℤ))
    (hsource : ∀ j<n, μ (base+j)=φ 0 (E.word j))
    (hpowers : Powers μ powers (2*N))
    (hd : d+1≤lim.depth)
    (hcoord : ∀ k (hk : k<N), ∀ μ' : ℕ→ℤ,
      (∀ j<n, μ' (a+j)=(address (E.word j) : ℤ)) → Powers μ' powers (2*N) →
      (∀ j<n, μ' (base+k*n+j)=φ k (E.word j)) →
      Meets lim P pCoord (d+1)
        [N,low (⟨k,hk⟩ : Fin N),high (⟨k,hk⟩ : Fin N),a,n,powers,L,keyBase,
          base+k*n,base+(k+1)*n] μ' (LightTernaryBankCoordinate.time N L n)
        (fun _ μ'' => (∀ j<n, μ'' (base+(k+1)*n+j)=φ (k+1) (E.word j)) ∧
          LightTernaryBankCoordinate.Preserved μ' μ'' keyBase n (base+(k+1)*n))) :
    Meets lim P pMain d [N,a,n,powers,L,keyBase,base] μ (time N L n)
      (fun _ μ' => Stages E φ base N μ' ∧ Preserved μ μ' keyBase n base N ∧ Powers μ' powers (2*N)) := by sorry
