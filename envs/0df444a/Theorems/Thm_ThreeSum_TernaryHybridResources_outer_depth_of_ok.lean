-- Prove2me | Theorems.Thm_ThreeSum_TernaryHybridResources_outer_depth_of_ok
-- name    : ThreeSum.TernaryHybridResources.outer_depth_of_ok
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:39:43.118352+00:00
-- url     : https://prove2.me/theorems/a668bd98-9705-4194-bba8-60e5bab85405
-- title:
--   Ternary Hybrid Resources: outer depth of ok
-- statement:
--   The Ternary Hybrid Resources construction uses the outer depth of ok property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryHybridResources.lean#L72-L76
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryHybridResources.lean#L72-L76

import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_LightBruteThreeSum
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_ThreeSum_TernaryHybridResources
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryHybridResources
open Light StageBounds ArithmeticStageBounds
set_option maxHeartbeats 1700000
set_option maxRecDepth 16000
variable (fastNeed : ℕ → ℕ → Light.Need)

theorem ThreeSum.TernaryHybridResources.outer_depth_of_ok {lim : Limits} {κ cutoff n U free d : ℕ}
    (H : (need fastNeed κ cutoff n U).Ok lim free d) : d+2<lim.depth := by sorry
