-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredConcreteFinalCall_reporter_eq
-- name    : ThreeSum.WeightedGlobalColoredConcreteFinalCall.reporter_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:38:06.172865+00:00
-- url     : https://prove2.me/theorems/bbe5a7b4-3131-44f2-a71e-1e5ad0465975
-- title:
--   Weighted Global Colored Concrete Final Call: reporter eq
-- statement:
--   The Weighted Global Colored Concrete Final Call construction uses the reporter eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredConcreteFinalCall.lean#L47-L52
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredConcreteFinalCall.lean#L47-L52

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredFinalCall
import Definitions.Def_Submission_Weighted_Global_TernaryColoredFinalReady
import Definitions.Def_Submission_Weighted_Global_TernaryColoredConcreteFinalCall
import Theorems.Thm_ThreeSum_SharedReportingBankData_Tables_reporting
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseBudget_threshold
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseFrames_output
import Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryTimeMonotone_selected
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_initial
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSelectedCollisions_selected

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredConcreteFinalCall
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalConcreteProfile WeightedGlobalLocalParameters WeightedGlobalColoredLoopSetup
open WeightedGlobalColoredTerminalReceipt WeightedGlobalColoredFinalReady
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000
variable {κ : ℕ}
variable (P : Profile κ) (n free menu c : ℕ) (A B C : List ℤ) (initial : ℕ→ℤ)
variable [Fact (Irreducible (WeightedGlobalComputedExtensionMenu.modulus P.p (dim P n) c))]

theorem ThreeSum.WeightedGlobalColoredConcreteFinalCall.reporter_eq :
    let S:=WeightedGlobalArenaSourceSetup.setup (r:=rounds P n) P.maps P.threshold P.cap P.output
      (selected P n free menu c A B C initial)
    LightWeightedGlobalPreparedPostSelection.closedProgram
      S.left.xs S.left.ys S.left.zs S.right.xs S.right.ys S.right.zs P.H=
        WeightedGlobalExecutable.reporting P.maps P.cap P.K := by sorry
