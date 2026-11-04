-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredPostABI_compact_argv
-- name    : ThreeSum.WeightedGlobalColoredPostABI.compact_argv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T18:10:35.816654+00:00
-- url     : https://prove2.me/theorems/65ecc996-42ee-410f-8303-8a0a319195a4
-- title:
--   Weighted Global Colored Post ABI: compact argv
-- statement:
--   Compact counts change only the two source-count words in the live ABI.
--   Frontend value/time caps are proof data and carry no runtime word.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPostABI.lean#L97-L103
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPostABI.lean#L97-L103

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryColoredSolver
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFinalSolver
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPostABI
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredPostABI
open Light LightWeightedGlobalColoredSolver WeightedGlobalArenaLayout
set_option maxRecDepth 24000
set_option maxHeartbeats 5000000

theorem ThreeSum.WeightedGlobalColoredPostABI.compact_argv {p m F r : ℕ} [Fact p.Prime]
    (maps : Fin F→WeightedGlobalCoverGoodMaps.Weight m p) (τ cap : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : WeightedGlobalArenaSourceSetup.Input) (nB nC : ℕ) :
    (LightWeightedGlobalCompactReporter.zeroCounts
      (WeightedGlobalArenaSourceSetup.setup (r := r) maps τ cap Q {I with nB:=nB,nC:=nC})).argv=
    (LightWeightedGlobalCompactReporter.zeroCounts
      (WeightedGlobalArenaSourceSetup.setup (r := r) maps τ cap Q I)).argv := by sorry
