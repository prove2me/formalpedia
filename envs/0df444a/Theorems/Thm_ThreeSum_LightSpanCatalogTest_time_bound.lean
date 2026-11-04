-- Prove2me | Theorems.Thm_ThreeSum_LightSpanCatalogTest_time_bound
-- name    : ThreeSum.LightSpanCatalogTest.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:51:42.42025+00:00
-- url     : https://prove2.me/theorems/4168d855-2232-4274-823e-89f6d27f2a8a
-- title:
--   Light Span Catalog Test: time bound
-- statement:
--   The Light Span Catalog Test construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSpanCatalogTest.lean#L178-L180
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSpanCatalogTest.lean#L178-L180

import Definitions.Def_Submission_ThreeSum_LightSpanCatalogStep
import Definitions.Def_Submission_ThreeSum_TernaryOriginalSpanCatalog
import Definitions.Def_Submission_ThreeSum_LightSpanCatalogTest
import Theorems.Thm_ThreeSum_LightSmallDivide_time_bound
import Theorems.Thm_ThreeSum_LightSpanCatalogStep_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPass_time_bound

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightSpanCatalogTest
open Light
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightSpanCatalogTest.time_bound (J n : ℕ) : time J n≤300*(n+1)*(J+1) := by sorry
