-- Prove2me | Theorems.Thm_ThreeSum_LightSwitchScalar_scalar_safe_w3sum_ac885d1
-- name    : ThreeSum.LightSwitchScalar.scalar_safe_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:35:36.483053+00:00
-- url     : https://prove2.me/theorems/3ffe842f-f147-4a5d-b614-d13f6564e217
-- title:
--   Light Switch Scalar: scalar safe
-- statement:
--   The Light Switch Scalar construction uses the scalar safe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSwitchScalar.lean#L62-L76
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSwitchScalar.lean#L62-L76

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightSwitchScalar
set_option autoImplicit false
open ThreeSum ThreeSum.LightSwitchScalar
open Light
set_option maxHeartbeats 1600000

theorem ThreeSum.LightSwitchScalar.scalar_safe_w3sum_ac885d1 {lim : Limits} {B : ℕ} (hB : 2 ≤ B) (σ : State)
    (hvars : ∀ i, |σ.loc i| ≤ (B : ℤ)) (e : Expr) (he : Small B e)
    (hword : ((B^e.cost : ℕ) : ℤ) ≤ lim.word) : e.Safe lim σ := by sorry
