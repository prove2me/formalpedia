-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_weighted_count_spec
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.weighted_count_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:13:22.482763+00:00
-- url     : https://prove2.me/theorems/a522b5c8-3702-4c07-8b12-23b3679b36e6
-- title:
--   weighted_count_spec
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/CountFrontend.lean#L184-L202
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/CountFrontend.lean#L184-L202

import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GroupBankResources
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_WantedRows
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_CountFrontend
import Theorems.Thm_Light_MatAt_keep
import Theorems.Thm_Light_SegN_keep
import Theorems.Thm_Light_Seg_keep
import Theorems.Thm_Light_VecAt_keep
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedWantedQuery_weighted_count_spec

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.WeightedBankEnumeration (cacheCost)
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.WeightedBankStageModel
open ThreeSum.LightWeightedNearPair ThreeSum.LightWeightedWantedRowDispatch ThreeSum.LightWeightedPreparedState
set_option maxHeartbeats 8000000
set_option maxRecDepth 18000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.weighted_count_spec {lim : Limits} {P : Program}
    {N a b pMain d t count dst keep : ℕ} (argv : List ℤ) (μ : ℕ→ℤ)
    (f g : ℕ→TritWord N→ℤ) (group : ℕ→ℕ) (Q : ℕ→TritWord N)
    (hf : ∀ j<count, ∀ A, f (group j) A≠0 → rank A=a)
    (hg : ∀ j<count, ∀ B, g (group j) B≠0 → rank B=b)
    (hQ : ∀ j<count, rank (Q j)=a+b)
    (h : Meets lim P pMain d argv μ t (fun _ ν => Kept μ ν keep ∧ ∀ j<count,
      ν (dst+j)=LightWeightedWantedRows.score
        (fun k A => ThreeSum.TernaryConvolution.factorial A*f k A)
        (fun k B => ThreeSum.TernaryConvolution.factorial B*g k B) group Q j)) :
    Meets lim P pMain d argv μ t (fun _ ν => Kept μ ν keep ∧ ∀ j<count,
      ν (dst+j)=ThreeSum.TernaryConvolution.factorial (Q j)*
        ThreeSum.TernaryConvolution.convolution (f (group j)) (g (group j)) (Q j)) := by sorry
