-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalTensorHeader_args_safe
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalTensorHeader.args_safe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:39:13.987718+00:00
-- url     : https://prove2.me/theorems/c93682c3-9d01-4b95-a9fe-523bceb21f56
-- title:
--   args_safe
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryTensorHeader.lean#L13-L26
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryTensorHeader.lean#L13-L26

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryTensorDriverSyntax
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryTensorHeader
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalTensorHeader
open Light LightWeightedGlobalTensorDriver

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalTensorHeader.args_safe {lim : Limits} (σ : State) (config : ℕ)
    (hconfig : σ.loc 0=(config : ℤ))
    (hspace : config+106≤lim.space) (hw : (lim.space : ℤ)≤lim.word) :
    ∀ e∈countArgs, e.Safe lim σ := by sorry
