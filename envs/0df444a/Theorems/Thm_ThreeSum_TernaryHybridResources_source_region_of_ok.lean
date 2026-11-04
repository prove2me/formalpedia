-- Prove2me | Theorems.Thm_ThreeSum_TernaryHybridResources_source_region_of_ok
-- name    : ThreeSum.TernaryHybridResources.source_region_of_ok
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:39:53.089236+00:00
-- url     : https://prove2.me/theorems/25357e10-80e6-42a2-bad2-d06dab3ae3cf
-- title:
--   Ternary Hybrid Resources: source region of ok
-- statement:
--   The Ternary Hybrid Resources construction uses the source region of ok property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryHybridResources.lean#L78-L82
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryHybridResources.lean#L78-L82

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

theorem ThreeSum.TernaryHybridResources.source_region_of_ok {lim : Limits} {κ cutoff n U src free d : ℕ}
    (H : (need fastNeed κ cutoff n U).Ok lim free d) (hsrc : src+n≤free) :
    src+n≤lim.space ∧ (free : ℤ)≤lim.word := by sorry
