-- Prove2me | Theorems.Thm_ThreeSum_TernaryHybridResources_polyBound_substitute_pow
-- name    : ThreeSum.TernaryHybridResources.polyBound_substitute_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:39:58.155787+00:00
-- url     : https://prove2.me/theorems/34b52c78-3d11-4809-8fbe-21a4a5737fbc
-- title:
--   Ternary Hybrid Resources: poly Bound substitute pow
-- statement:
--   The Ternary Hybrid Resources construction uses the poly Bound substitute pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryHybridResources.lean#L94-L113
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryHybridResources.lean#L94-L113

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

theorem ThreeSum.TernaryHybridResources.polyBound_substitute_pow (s e κ n U : ℕ) :
    Light.polyBound s e [n,n^κ]≤Light.polyBound (s+e) ((κ+1)*e) [n,U] := by sorry
