-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaArgumentBudget_polyNeed
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaArgumentBudget.polyNeed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T13:50:28.874054+00:00
-- url     : https://prove2.me/theorems/a32a13bf-59c9-46f4-9306-1468b3549553
-- title:
--   polyNeed
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaArgumentBudget.lean#L109-L131
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaArgumentBudget.lean#L109-L131

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaArgumentWords
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceControlBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaArgumentBudget
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedFrontendResources_polyNeed
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalFrontendResources_polyNeed
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalMomentChannelResources_polyNeed
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalMomentDetectorResources_polyNeed

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaArgumentBudget
open Light WeightedGlobalArenaSourceSetup WeightedGlobalArenaArgumentWords WeightedGlobalArenaSourceControlBudget
open WeightedGlobalLocalParameters

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaArgumentBudget.polyNeed (m p F M : ℕ) (hM : 1<M) : PolyNeed (need m p F M) := by sorry
