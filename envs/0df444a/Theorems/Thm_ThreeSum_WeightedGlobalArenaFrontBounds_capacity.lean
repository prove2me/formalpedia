-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaFrontBounds_capacity
-- name    : ThreeSum.WeightedGlobalArenaFrontBounds.capacity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:04:42.43134+00:00
-- url     : https://prove2.me/theorems/3643c0d8-a676-4509-bf17-38e3c8e24764
-- title:
--   Weighted Global Arena Front Bounds: capacity
-- statement:
--   The Weighted Global Arena Front Bounds construction uses the capacity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFrontBounds.lean#L102-L141
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFrontBounds.lean#L102-L141

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCountReady
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFrontBounds
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Seed_finish
import Theorems.Thm_ThreeSum_WeightedSourceCountExecutionFactory_Seed_finish

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaFrontBounds
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaSourceSetup WeightedGlobalArenaSourceBounds
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters
set_option maxHeartbeats 6000000
variable {p m F r : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaFrontBounds.capacity {lim : Light.Limits} {d : ℕ}
    (maps : Fin F→Weight m p) (τ cap M b K H drift scale : ℕ)
    (I : Input) (n U : ℕ) (hnB : I.nB≤n) (hnC : I.nC≤n)
    (hO : I.requesterCount≤n*2^(LightWeightedGlobalDimensions.J M b n U))
    (hweight : I.weightCap≤weight H (4^fixedLength m) U)
    (HC : Fits I.capacity (numbers maps τ cap M b K H drift scale n U r))
    (hend : WeightedGlobalArenaLayout.finish I.free I.capacity≤lim.space)
    (hprefix : I.prefixFree=WeightedGlobalArenaLayout.addr I.free I.capacity 13)
    (hw : (I.capacity : ℤ)≤lim.word) (hd : d+I.capacity≤lim.depth)
    (htime : WeightedGlobalArenaCountReady.queryTime (m := m) (r := r) I
      (valueCap (r := r) maps cap I)≤I.queryTime) :
    WeightedGlobalArenaCountReady.Capacity (lim := lim) (d := d) (r := r) maps τ cap I := by sorry
