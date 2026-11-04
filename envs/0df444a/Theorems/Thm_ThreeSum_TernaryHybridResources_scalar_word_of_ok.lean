-- Prove2me | Theorems.Thm_ThreeSum_TernaryHybridResources_scalar_word_of_ok
-- name    : ThreeSum.TernaryHybridResources.scalar_word_of_ok
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:01:31.70469+00:00
-- url     : https://prove2.me/theorems/3a0dc799-db73-45ae-a8bb-73d444e76ef6
-- title:
--   Ternary Hybrid Resources: scalar word of ok
-- statement:
--   The Ternary Hybrid Resources construction uses the scalar word of ok property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryHybridResources.lean#L56-L62
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryHybridResources.lean#L56-L62

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

theorem ThreeSum.TernaryHybridResources.scalar_word_of_ok {lim : Limits} {κ cutoff n U free d : ℕ}
    (H : (need fastNeed κ cutoff n U).Ok lim free d) :
    ((n+κ+cutoff+U+(n+1)^(κ+1)+10 : ℕ) : ℤ)≤lim.word := by sorry
