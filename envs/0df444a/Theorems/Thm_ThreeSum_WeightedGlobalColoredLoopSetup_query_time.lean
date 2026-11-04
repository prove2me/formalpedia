-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredLoopSetup_query_time
-- name    : ThreeSum.WeightedGlobalColoredLoopSetup.query_time
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:11:19.218827+00:00
-- url     : https://prove2.me/theorems/37e8486c-de35-4387-a6ba-a73d3254ca8a
-- title:
--   Weighted Global Colored Loop Setup: query time
-- statement:
--   The Weighted Global Colored Loop Setup construction uses the query time property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLoopSetup.lean#L89-L97
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLoopSetup.lean#L89-L97

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

theorem ThreeSum.WeightedGlobalColoredLoopSetup.query_time (P : Profile κ) (n free : ℕ) (A B C : List ℤ) (j : ℕ) (hj : j≤rounds P n) :
    WeightedGlobalArenaCountReady.queryTime (m:=P.m) (r:=j) (input P n free A B C)
      (valueCap (r:=j) P.maps P.cap (input P n free A B C))≤
      (input P n free A B C).queryTime := by sorry
