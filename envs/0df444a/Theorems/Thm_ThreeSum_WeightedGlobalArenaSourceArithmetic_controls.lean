-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceArithmetic_controls
-- name    : ThreeSum.WeightedGlobalArenaSourceArithmetic.controls
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:08:28.486918+00:00
-- url     : https://prove2.me/theorems/0bb75617-22d8-497d-aec2-1e98f6a9001a
-- title:
--   Weighted Global Arena Source Arithmetic: controls
-- statement:
--   The Weighted Global Arena Source Arithmetic construction uses the controls property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceArithmetic.lean#L50-L74
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceArithmetic.lean#L50-L74

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceControls
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceLayout
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceArithmetic
import Theorems.Thm_ThreeSum_WeightedFrontendResources_controls
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceControls_controls
import Theorems.Thm_ThreeSum_WeightedGlobalFrontendResources_controls

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSourceArithmetic
open Light WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaSourceSetup WeightedGlobalArenaSourceBounds
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters WeightedGlobalNativeCompleteFrontend
open LightTernarySourceHost WeightedGlobalArenaLayout
set_option maxHeartbeats 6000000
variable {p m F r : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaSourceArithmetic.controls {lim : Limits} {d : ℕ} (maps : Fin F→Weight m p) (τ cap M b K H drift scale : ℕ)
    (I : Input) (n U : ℕ) (hnB : I.nB≤n) (hnC : I.nC≤n)
    (hweight : I.weightCap≤weight H (4^fixedLength m) U)
    (HC : Fits I.capacity (numbers maps τ cap M b K H drift scale n U r))
    (hw : (I.capacity : ℤ)≤lim.word) (hd : d+I.capacity≤lim.depth) (right : Bool) :
    WeightedGlobalArenaSourceControls.Controls (r := r) maps cap I right lim d := by sorry
