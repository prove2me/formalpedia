-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedWantedQuery_weighted_count_spec
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedWantedQuery.weighted_count_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:47:51.531573+00:00
-- url     : https://prove2.me/theorems/10d36c1b-d04a-4b40-a485-9e5969c827b1
-- title:
--   weighted_count_spec
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/WantedQuery.lean#L162-L175
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/WantedQuery.lean#L162-L175

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearPair
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrozenPhysical
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankAssembly
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_WantedQuery
import Theorems.Thm_Light_MatAt_keep
import Theorems.Thm_Light_SegN_keep
import Theorems.Thm_Light_Seg_keep
import Theorems.Thm_Light_VecAt_keep

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedWantedQuery
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.WeightedBankStageModel
open ThreeSum.WeightedBankEnumeration (cacheCost)
open ThreeSum.LightWeightedNearPair
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedWantedQuery.weighted_count_spec {N a b pMain d t : ℕ} (argv : List ℤ) (μ : ℕ→ℤ)
    (f g : TritWord N→ℤ) (Q : TritWord N) (keep : ℕ)
    (hf : ∀ A, f A≠0 → rank A=a) (hg : ∀ B, g B≠0 → rank B=b)
    (hQ : rank Q=a+b)
    (hquery : Meets lim P pMain d argv μ t (fun v ν =>
      v=stageValue N (H (fun A => ThreeSum.TernaryConvolution.factorial A*f A)
        (fun B => ThreeSum.TernaryConvolution.factorial B*g B)) Q ∧ Kept μ ν keep)) :
    Meets lim P pMain d argv μ t (fun v ν =>
      v=ThreeSum.TernaryConvolution.factorial Q*ThreeSum.TernaryConvolution.convolution f g Q ∧
        Kept μ ν keep) := by sorry
