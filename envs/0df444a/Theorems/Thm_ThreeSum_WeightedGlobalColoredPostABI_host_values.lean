-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredPostABI_host_values
-- name    : ThreeSum.WeightedGlobalColoredPostABI.host_values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T18:13:24.547045+00:00
-- url     : https://prove2.me/theorems/4aa9d8d0-14fe-4104-af73-4acc7d9fc0e6
-- title:
--   Weighted Global Colored Post ABI: host values
-- statement:
--   The Weighted Global Colored Post ABI construction uses the host values property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPostABI.lean#L24-L40
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPostABI.lean#L24-L40

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

theorem ThreeSum.WeightedGlobalColoredPostABI.host_values {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (loc μ : ℕ→ℤ) (host : ℕ) (hloc : loc 10=(host : ℤ))
    (hreads : ∀ i<106,i≠11→i≠34→
      μ (host+i)=(LightWeightedGlobalCompactReporter.zeroCounts S).argv.getD i 0) :
    hostArgs.map (fun e=>e.val ⟨loc,μ⟩)=(LightWeightedGlobalCompactReporter.zeroCounts S).argv := by sorry
