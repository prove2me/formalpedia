-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaReporterBounds_compact_abs
-- name    : ThreeSum.WeightedGlobalArenaReporterBounds.compact_abs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:14:08.816018+00:00
-- url     : https://prove2.me/theorems/cefa89ec-b6e1-4f97-9afd-f1ae73e4ffc5
-- title:
--   Weighted Global Arena Reporter Bounds: compact abs
-- statement:
--   The Weighted Global Arena Reporter Bounds construction uses the compact abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaReporterBounds.lean#L19-L23
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaReporterBounds.lean#L19-L23

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPostSelection
import Definitions.Def_Submission_Weighted_Global_TernaryMomentChannelResources
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_Submission_Weighted_Global_TernaryArenaReporterBounds
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaReporterBounds
open Light WeightedGlobalArenaLayout LightOriginalSurvivors
open WeightedGlobalNativeMomentBounds WeightedGlobalMomentWeightBounds

theorem ThreeSum.WeightedGlobalArenaReporterBounds.compact_abs (keys : ℕ→ℕ) (values : ℕ→ℤ) (n U : ℕ)
    (h : ∀ i<n, |values i|≤(U : ℤ)) :
    ∀ j<(indices keys n).length, |LightWeightedGlobalPostSelection.compact keys values n j|≤(U : ℤ) := by sorry
