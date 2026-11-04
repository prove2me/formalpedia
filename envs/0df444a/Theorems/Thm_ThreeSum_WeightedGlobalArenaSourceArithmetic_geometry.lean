-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceArithmetic_geometry
-- name    : ThreeSum.WeightedGlobalArenaSourceArithmetic.geometry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:07:30.702759+00:00
-- url     : https://prove2.me/theorems/947534ac-0879-4eb1-a242-e66073aaf976
-- title:
--   Weighted Global Arena Source Arithmetic: geometry
-- statement:
--   The Weighted Global Arena Source Arithmetic construction uses the geometry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceArithmetic.lean#L20-L48
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceArithmetic.lean#L20-L48

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceControls
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceLayout
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceArithmetic
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Seed_finish
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceLayout_geometry
import Theorems.Thm_ThreeSum_WeightedSourceCountExecutionFactory_Seed_finish

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSourceArithmetic
open Light WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaSourceSetup WeightedGlobalArenaSourceBounds
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters WeightedGlobalNativeCompleteFrontend
open LightTernarySourceHost WeightedGlobalArenaLayout
set_option maxHeartbeats 6000000
variable {p m F r : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaSourceArithmetic.geometry {lim : Limits} (maps : Fin F→Weight m p) (τ cap M b K H drift scale : ℕ)
    (I : Input) (n U : ℕ) (hnB : I.nB≤n) (hnC : I.nC≤n)
    (HC : Fits I.capacity (numbers maps τ cap M b K H drift scale n U r))
    (hend : finish I.free I.capacity≤lim.space) (right : Bool) :
    WeightedGlobalArenaSourceLayout.Geometry (source (r := r) maps cap I right) lim.space := by sorry
