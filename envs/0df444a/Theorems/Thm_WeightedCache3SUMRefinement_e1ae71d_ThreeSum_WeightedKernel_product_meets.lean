-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedKernel_product_meets
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedKernel.product_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:31:00.963113+00:00
-- url     : https://prove2.me/theorems/877184fb-0311-4cf3-b729-ca36936176a7
-- title:
--   product_meets
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/KernelProgram.lean#L186-L194
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/KernelProgram.lean#L186-L194

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedKernel.product_meets {d a b dst n U V : ℕ}
    (μ : ℕ→ℤ) (hw : (lim.space : ℤ)≤lim.word)
    (ha : a+n≤lim.space) (hb : b+n≤lim.space) (hdst : dst+n≤lim.space)
    (hsepA : LightArray.SourceSafe a dst n) (hsepB : LightArray.SourceSafe b dst n)
    (hA : ∀ j<n, |μ (a+j)|≤U) (hB : ∀ j<n, |μ (b+j)|≤V)
    (hword : (U : ℤ)*(V : ℤ)≤lim.word) :
    Meets lim program 35 d [a,b,dst,n] μ (LightTernaryProduct.time n)
      (fun _ ν => (∀ j<n, ν (dst+j)=μ (a+j)*μ (b+j)) ∧ SameOutside μ ν dst n) := by sorry
