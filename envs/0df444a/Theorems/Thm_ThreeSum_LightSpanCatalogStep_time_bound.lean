-- Prove2me | Theorems.Thm_ThreeSum_LightSpanCatalogStep_time_bound
-- name    : ThreeSum.LightSpanCatalogStep.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:45:20.038881+00:00
-- url     : https://prove2.me/theorems/b91719c6-158e-471f-9e41-2aa7938162d6
-- title:
--   Light Span Catalog Step: time bound
-- statement:
--   The Light Span Catalog Step construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSpanCatalogStep.lean#L181-L198
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSpanCatalogStep.lean#L181-L198

import Definitions.Def_Submission_ThreeSum_LightSpanAxpy
import Definitions.Def_Submission_ThreeSum_LightSpanCatalogStep
import Theorems.Thm_ThreeSum_LightSmallDivide_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPass_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightSpanCatalogStep
open Light
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightSpanCatalogStep.time_bound (J p n : ℕ) :
    time J p n≤(p+1)*(n+1)*(J+1)*(LightPrimeCoefficient.mulAddTime p+500) := by sorry
