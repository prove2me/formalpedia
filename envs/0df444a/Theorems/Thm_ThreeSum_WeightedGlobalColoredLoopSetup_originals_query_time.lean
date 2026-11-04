-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredLoopSetup_originals_query_time
-- name    : ThreeSum.WeightedGlobalColoredLoopSetup.originals_query_time
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:19:29.123808+00:00
-- url     : https://prove2.me/theorems/d026ba7d-62e4-478f-9b49-a8170725576f
-- title:
--   Weighted Global Colored Loop Setup: originals query time
-- statement:
--   The Weighted Global Colored Loop Setup construction uses the originals query time property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLoopSetup.lean#L99-L108
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLoopSetup.lean#L99-L108

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryConcreteProfile
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLoopState
import Definitions.Def_Submission_Weighted_Global_TernaryPreparedOriginals
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixPrepareAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectorAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopSetup
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredLoopSetup
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalConcreteProfile WeightedGlobalLocalParameters
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000
variable {κ : ℕ}

theorem ThreeSum.WeightedGlobalColoredLoopSetup.originals_query_time {p : ℕ} [Fact p.Prime] {E : Type*} [Field E] [Fintype E]
    [DecidableEq E] [Algebra (ZMod p) E] {I : Input} {A : Inputs}
    {seedCount featureBound tagBound positionCap : ℕ} {ell : E→ₗ[ZMod p] ZMod p}
    {seeds : ℕ→E×E} {L R O : ℕ→ℕ→ℤ} {μ : ℕ→ℤ}
    (H : WeightedGlobalArenaPrefixInputs.Originals I A seedCount featureBound tagBound positionCap ell seeds L R O μ)
    (t : ℕ) :
    WeightedGlobalArenaPrefixInputs.Originals {I with queryTime:=t} A seedCount featureBound tagBound positionCap ell seeds L R O μ := by sorry
