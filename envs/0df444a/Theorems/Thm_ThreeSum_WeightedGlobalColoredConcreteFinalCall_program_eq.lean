-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredConcreteFinalCall_program_eq
-- name    : ThreeSum.WeightedGlobalColoredConcreteFinalCall.program_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:38:25.922207+00:00
-- url     : https://prove2.me/theorems/30029d9d-e0cd-4c0c-9628-0bb604bfad38
-- title:
--   Weighted Global Colored Concrete Final Call: program eq
-- statement:
--   The Weighted Global Colored Concrete Final Call construction uses the program eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredConcreteFinalCall.lean#L41-L42
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredConcreteFinalCall.lean#L41-L42

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredFinalCall
import Definitions.Def_Submission_Weighted_Global_TernaryColoredFinalReady
import Definitions.Def_Submission_Weighted_Global_TernaryColoredConcreteFinalCall
import Theorems.Thm_ThreeSum_SharedReportingBankData_Tables_reporting

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredConcreteFinalCall
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalConcreteProfile WeightedGlobalLocalParameters WeightedGlobalColoredLoopSetup
open WeightedGlobalColoredTerminalReceipt WeightedGlobalColoredFinalReady
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000
variable {κ : ℕ}

theorem ThreeSum.WeightedGlobalColoredConcreteFinalCall.program_eq (P : Profile κ) : P.color=
    ReportingHostRelocation.program (pre P) (WeightedGlobalExecutable.reporting P.maps P.cap P.K)++suffix P := by sorry
