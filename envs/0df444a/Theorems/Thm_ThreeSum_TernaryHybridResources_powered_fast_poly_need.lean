-- Prove2me | Theorems.Thm_ThreeSum_TernaryHybridResources_powered_fast_poly_need
-- name    : ThreeSum.TernaryHybridResources.powered_fast_poly_need
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:40:09.247055+00:00
-- url     : https://prove2.me/theorems/416141b3-7854-4e3a-87fe-b139ea8d2675
-- title:
--   Ternary Hybrid Resources: powered fast poly need
-- statement:
--   The Ternary Hybrid Resources construction uses the powered fast poly need property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryHybridResources.lean#L119-L124
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryHybridResources.lean#L119-L124

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
noncomputable section

theorem ThreeSum.TernaryHybridResources.powered_fast_poly_need (hf : Light.PolyNeed fastNeed) (κ : ℕ) : Light.PolyNeed (poweredFastNeed fastNeed κ) := by sorry
