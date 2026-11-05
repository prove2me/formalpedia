-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedKernel_frozen_query_meets
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedKernel.frozen_query_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:30:57.956553+00:00
-- url     : https://prove2.me/theorems/39bb3fb2-a444-4629-aaef-d9cf01c31d4e
-- title:
--   frozen_query_meets
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/KernelProgram.lean#L148-L184
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/KernelProgram.lean#L148-L184

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearSourceWords
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankStages
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankCanonical
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_LightEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_LightNearEnumerationMain
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrozenPhysical
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearSetup
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_KernelProgram
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedKernel
open Light ThreeSum.LightSubsetAddress
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.WeightedBankEnumeration (cacheCost)
open ThreeSum.TernaryCodeSemantics ThreeSum.WeightedPhysicalEuler
open ThreeSum.WeightedBankStageModel ThreeSum.TernaryFrozenQueryStages
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {lim : Limits}

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedKernel.frozen_query_meets {N : ℕ}
    (T bankCodes bankCount bankValues nearCodes nearCount nearValues powers L U : ℕ)
    (bankWords nearWords : ℕ→TritWord N) (H : TritWord N→ℤ) (Q : TritWord N) (μ : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word)
    (hbankCodesSpace : bankCodes+bankCount≤lim.space)
    (hbankValuesSpace : bankValues+(N+1)*bankCount≤lim.space)
    (hnearCodesSpace : nearCodes+nearCount≤lim.space)
    (hnearValuesSpace : nearValues+nearCount≤lim.space)
    (hspace : powers+(2*N+1)≤lim.space)
    (hword : ((bankCount+nearCount+2^(2*N+1)+16 : ℕ) : ℤ)≤lim.word)
    (hNword : 2*(N : ℤ)+3≤lim.word)
    (hcutWord : (T : ℤ)+1≤lim.word)
    (hcostWord : ((2740*N+3000 : ℕ) : ℤ)≤lim.word)
    (hvalueWord : 4*((4^N : ℕ) : ℤ)*(U : ℤ)+3≤lim.word)
    (hpowers : Powers μ powers (2*N)) (hL : L≤2*N)
    (hbankSmall : bankCount<2^L) (hnearSmall : nearCount<2^L)
    (hH : ∀ R, |H R|≤(U : ℤ))
    (hbankRead : ∀ j<bankCount, μ (bankCodes+j)=(address (bankWords j) : ℤ))
    (hbankSorted : ∀ i j, i<j → j<bankCount → address (bankWords i)<address (bankWords j))
    (hbankPresent : ∀ R : TritWord N, WeightedFrozenQueryCost.cacheCost R≤T → ∃ j<bankCount, bankWords j=R)
    (hbankValues : ∀ K≤N, ∀ j<bankCount, μ (bankValues+K*bankCount+j)=stageValue K H (bankWords j))
    (hnearRead : ∀ j<nearCount, μ (nearCodes+j)=(address (nearWords j) : ℤ))
    (hnearSorted : ∀ i j, i<j → j<nearCount → address (nearWords i)<address (nearWords j))
    (hnearPresent : ∀ R : TritWord N, Below R Q → T<WeightedFrozenQueryCost.cacheCost R → ∃ j<nearCount, nearWords j=R)
    (hnearValues : ∀ j<nearCount, μ (nearValues+j)=H (nearWords j)) :
    ∀ K≤N, ∀ R : TritWord N, Below R Q → ∀ d, d+K+2*N+L+3≤lim.depth →
      Meets lim program 33 d
        (LightWeightedFrozenQuery.inputs N K (WeightedFrozenQueryCost.cacheCost R) T (address R) bankCodes bankCount bankValues
          nearCodes nearCount nearValues powers L) μ (LightWeightedFrozenQuery.queryTime L T K R)
        (fun v μ' => v=stageValue K H R ∧ μ'=μ) := by sorry
