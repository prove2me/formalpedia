-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaReporterBounds_arena_geometry
-- name    : ThreeSum.WeightedGlobalArenaReporterBounds.arena_geometry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:14:21.92542+00:00
-- url     : https://prove2.me/theorems/40851cc4-7986-405c-98a5-fcaf400d2877
-- title:
--   Weighted Global Arena Reporter Bounds: arena geometry
-- statement:
--   Reporting reuses the tensor region after the final seed is selected.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaReporterBounds.lean#L83-L97
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaReporterBounds.lean#L83-L97

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPostSelection
import Definitions.Def_Submission_Weighted_Global_TernaryMomentChannelResources
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_Submission_Weighted_Global_TernaryArenaReporterBounds
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Seed_finish
import Theorems.Thm_ThreeSum_WeightedSourceCountExecutionFactory_Seed_finish

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaReporterBounds
open Light WeightedGlobalArenaLayout LightOriginalSurvivors
open WeightedGlobalNativeMomentBounds WeightedGlobalMomentWeightBounds

theorem ThreeSum.WeightedGlobalArenaReporterBounds.arena_geometry {free C H count nl nr space : ℕ}
    (hcount : (2*H+1)*count≤C) (hterms : 2*H+1≤C)
    (hl : nl≤C) (hr : nr≤C) (hend : finish free C≤space) :
    addr free C 25+(2*H+1)*count≤addr free C 26 ∧
    addr free C 26+(2*H+1)≤space ∧
    addr free C 25+(2*H+1)*count≤addr free C 28 ∧
    addr free C 28+nl≤addr free C 29 ∧ addr free C 29+nr≤space ∧
    addr free C 28≤addr free C 53 ∧ addr free C 53+count≤space ∧
    addr free C 28≤space := by sorry
