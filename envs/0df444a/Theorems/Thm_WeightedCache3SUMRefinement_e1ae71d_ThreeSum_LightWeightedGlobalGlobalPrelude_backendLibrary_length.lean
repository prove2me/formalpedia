-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalGlobalPrelude_backendLibrary_length
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalGlobalPrelude.backendLibrary_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:34:31.987809+00:00
-- url     : https://prove2.me/theorems/39de92ea-ff50-4edb-a780-1a6a37df6229
-- title:
--   backendLibrary_length
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryGlobalPrelude.lean#L60-L61
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryGlobalPrelude.lean#L60-L61

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryDimensions
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightExtensionBackendSetup
import Definitions.Def_Submission_ThreeSum_LightScales
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryGlobalPrelude
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalGlobalPrelude
open Light

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalGlobalPrelude.backendLibrary_length (M b p K : ℕ) :
    (backendLibrary M b p K).length=48 := by sorry

attribute [defeq] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalGlobalPrelude.backendLibrary_length
