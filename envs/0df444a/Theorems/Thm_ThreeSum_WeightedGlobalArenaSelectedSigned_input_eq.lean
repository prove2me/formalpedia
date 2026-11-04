-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSelectedSigned_input_eq
-- name    : ThreeSum.WeightedGlobalArenaSelectedSigned.input_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:52:02.751044+00:00
-- url     : https://prove2.me/theorems/f864e8d5-704b-4845-b6e7-522305222c56
-- title:
--   Weighted Global Arena Selected Signed: input eq
-- statement:
--   Both the requester/carry occurrence count and its provenance match the
--   literal actual native-completeness input, including all repeated targets.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSelectedSigned.lean#L50-L75
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSelectedSigned.lean#L50-L75

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedTerminal
import Definitions.Def_Submission_Weighted_Global_TernarySignedFeatureHash
import Definitions.Def_Submission_Weighted_Global_TernaryArenaNativeComplete
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedSigned
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSelectedSigned
open TernarySignedReduction TernarySignedLayout WeightedGlobalNativeRequesterCoverage
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSelectedBudgets
open WeightedGlobalArenaSelectedTerminal WeightedGlobalArenaBudgetExistence WeightedGlobalCoverGoodMaps
set_option maxHeartbeats 5000000
variable {p m F : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaSelectedSigned.input_eq (I : Input) (A : Inputs) (s : State (p := p) A) (r U radix nA : ℕ)
    (X B C : ℕ→ℤ) :
    WeightedGlobalArenaSelectedTerminal.input (base I A.J nA) A s
      (left U radix A.J B) (right U radix A.J C) (requester U radix A.J X) r=
      WeightedGlobalArenaNativeComplete.input I U radix nA (selectedHash A s r) X B C := by sorry
