-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalControllerFactory_SpanGuard_run
-- name    : ThreeSum.LightWeightedGlobalControllerFactory.SpanGuard.run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:17:45.746385+00:00
-- url     : https://prove2.me/theorems/753c717b-42b1-4337-ae76-65ba920ea3a6
-- title:
--   Span Guard: run
-- statement:
--   The Span Guard construction uses the run property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryControllerFactory.lean#L133-L140
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryControllerFactory.lean#L133-L140

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedScoreFactory
import Definitions.Def_Submission_Weighted_Global_TernaryNativeTensorScore
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedController
import Definitions.Def_Submission_Weighted_Global_LightTernaryControllerFactory
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScoreFactory_Ready_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalTensorFactory_Ready_run
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Ready_run
import Theorems.Thm_ThreeSum_WeightedCountExecutionFactory_Ready_run
import Theorems.Thm_ThreeSum_WeightedSourceCountExecutionFactory_Ready_run
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalControllerFactory
open Light LightWeightedGlobalSeedScoreFactory
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedGlobalControllerFactory.SpanGuard.run {C : Config} [Fact C.p.Prime] {D : Data C} {lim : Limits}
    {depth newSpan : ℕ} {μ : ℕ→ℤ} (G : SpanGuard C D lim depth newSpan μ) :
    Meets lim LightStoredSpan.program 1 depth [C.catalog,C.catalogRows,C.row,newSpan,C.J,C.p]
      μ (LightSpanCatalogStep.time C.J C.p C.catalogRows) (fun _ ν=>SpanDone C D newSpan μ ν) := by sorry
