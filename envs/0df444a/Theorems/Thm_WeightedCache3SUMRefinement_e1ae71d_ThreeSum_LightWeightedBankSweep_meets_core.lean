-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedBankSweep_meets_core
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankSweep.meets_core
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:12:01.711196+00:00
-- url     : https://prove2.me/theorems/cd4843c2-dabc-4eb5-bd8d-ee6b207dac7d
-- title:
--   meets_core
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/BankSweep.lean#L38-L137
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/BankSweep.lean#L38-L137

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankCoordinate
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankSweep
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankSweep
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
set_option maxHeartbeats 5000000
variable {lim : Limits} {P : Program}

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankSweep.meets_core {N T n pMain pCoord a powers L keyBase base d : ℕ}
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
          base+k*n,base+(k+1)*n] μ' (LightWeightedBankCoordinate.time N L n)
        (fun _ μ'' => (∀ j<n, μ'' (base+(k+1)*n+j)=φ (k+1) (E.word j)) ∧
          LightWeightedBankCoordinate.Preserved μ' μ'' keyBase n (base+(k+1)*n))) :
    Meets lim P pMain d [N,a,n,powers,L,keyBase,base] μ (time N L n)
      (fun _ μ' => Stages E φ base N μ' ∧ Preserved μ μ' keyBase n base N ∧ Powers μ' powers (2*N)) := by sorry
