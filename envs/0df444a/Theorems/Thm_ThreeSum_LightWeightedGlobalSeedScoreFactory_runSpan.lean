-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScoreFactory_runSpan
-- name    : ThreeSum.LightWeightedGlobalSeedScoreFactory.runSpan
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:18:18.723203+00:00
-- url     : https://prove2.me/theorems/b02688a6-8f5f-4c73-a45a-4b9f4cf8157b
-- title:
--   Light Weighted Global Seed Score Factory: run Span
-- statement:
--   The Light Weighted Global Seed Score Factory construction uses the run Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernarySeedScoreFactory.lean#L273-L282
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernarySeedScoreFactory.lean#L273-L282

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedScore
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalDigitSpan
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchCount
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorFactoryScaled
import Definitions.Def_Submission_Weighted_Global_TernaryNativeTensorScore
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedScoreFactory
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalSeedScoreFactory
open Light
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {lim : Limits}

theorem ThreeSum.LightWeightedGlobalSeedScoreFactory.runSpan {C : Config} [Fact C.p.Prime] {D : Data C} {depth : ℕ} {μ : ℕ → ℤ}
    (G : AppendGuard C D lim depth μ) (H : SpanGuard C D lim μ) :
    Meets lim LightStoredSpan.program 6 (depth+1) [C.catalog,C.catalogRows,C.J,C.row] μ
      (LightSpanCatalogTest.time C.J C.catalogRows) (fun r ν => r=D.flag ∧ ν=μ) := by sorry
