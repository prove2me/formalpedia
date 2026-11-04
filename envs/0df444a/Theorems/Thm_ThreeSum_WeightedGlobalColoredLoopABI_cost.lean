-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredLoopABI_cost
-- name    : ThreeSum.WeightedGlobalColoredLoopABI.cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:11:14.173926+00:00
-- url     : https://prove2.me/theorems/ff0da9e7-b6d7-4aa7-9513-3c584f462b24
-- title:
--   Weighted Global Colored Loop ABI: cost
-- statement:
--   The Weighted Global Colored Loop ABI construction uses the cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLoopABI.lean#L55-L56
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLoopABI.lean#L55-L56

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLoopState
import Definitions.Def_Submission_Weighted_Global_LightTernaryColoredSolver
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopABI
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredLoopABI
open Light WeightedGlobalArenaLayout WeightedGlobalArenaLoop LightWeightedGlobalColoredSolver WeightedGlobalLocalParameters
variable {p m F K N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
set_option maxHeartbeats 1500000

theorem ThreeSum.WeightedGlobalColoredLoopABI.cost (m F p alpha2 alphaRank localQ R a b scale : ℕ) :
    ((loopArgs m F p alpha2 alphaRank localQ R a b scale).map Expr.cost).sum=23 := by sorry

attribute [defeq] ThreeSum.WeightedGlobalColoredLoopABI.cost
