-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalFastProgramBudget_full
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalFastProgramBudget.full
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:07:32.609197+00:00
-- url     : https://prove2.me/theorems/84358634-caf9-47e2-be1e-86b1ffb7160b
-- title:
--   full
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryFastProgramBudget.lean#L37-L45
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryFastProgramBudget.lean#L37-L45

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryFastProgramResources
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryFastProgramBudget
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalFastProgramBudget
open Light StageBounds ArithmeticStageBounds LightColorParametersCosts
open Filter
open scoped Topology

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalFastProgramBudget.full {m b p K κ : ℕ} [Fact p.Prime] (hm : 0<m) (hb : 1<b)
    {T : ℕ→ℕ} {a : ℝ} (hT : PowerBound T a) (ha : 0≤a) :
    PowerBound (fun n=>LightWeightedGlobalFastProgramProof.time (WeightedGlobalCoverScale.outputSize m) b p K κ (T n) n) a := by sorry
