-- Prove2me | Theorems.Thm_ThreeSum_TernaryHybridResources_power_word_of_ok
-- name    : ThreeSum.TernaryHybridResources.power_word_of_ok
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:06:44.648812+00:00
-- url     : https://prove2.me/theorems/74150874-0a0f-4727-a787-0849f00c0310
-- title:
--   Ternary Hybrid Resources: power word of ok
-- statement:
--   The Ternary Hybrid Resources construction uses the power word of ok property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryHybridResources.lean#L64-L70
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryHybridResources.lean#L64-L70

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

theorem ThreeSum.TernaryHybridResources.power_word_of_ok {lim : Limits} {κ cutoff n U free d i : ℕ}
    (H : (need fastNeed κ cutoff n U).Ok lim free d) (hi : i≤κ) : ((n^i : ℕ) : ℤ)≤lim.word := by sorry
