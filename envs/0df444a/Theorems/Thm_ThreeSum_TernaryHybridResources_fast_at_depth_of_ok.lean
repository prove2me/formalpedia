-- Prove2me | Theorems.Thm_ThreeSum_TernaryHybridResources_fast_at_depth_of_ok
-- name    : ThreeSum.TernaryHybridResources.fast_at_depth_of_ok
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:40:01.709036+00:00
-- url     : https://prove2.me/theorems/0a37004c-befb-4923-882d-06b2e8bb7ec2
-- title:
--   Ternary Hybrid Resources: fast at depth of ok
-- statement:
--   The Ternary Hybrid Resources construction uses the fast at depth of ok property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryHybridResources.lean#L34-L38
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryHybridResources.lean#L34-L38

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

theorem ThreeSum.TernaryHybridResources.fast_at_depth_of_ok {lim : Limits} {κ cutoff n U free d e : ℕ}
    (H : (need fastNeed κ cutoff n U).Ok lim free d) (he : e≤d+2) :
    (fastNeed n (n^κ)).Ok lim free e := by sorry
