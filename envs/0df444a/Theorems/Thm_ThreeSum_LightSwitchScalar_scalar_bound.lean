-- Prove2me | Theorems.Thm_ThreeSum_LightSwitchScalar_scalar_bound
-- name    : ThreeSum.LightSwitchScalar.scalar_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:35:35.609949+00:00
-- url     : https://prove2.me/theorems/f3dba9a2-c657-4af2-88c9-4529d3a2857b
-- title:
--   Light Switch Scalar: scalar bound
-- statement:
--   The Light Switch Scalar construction uses the scalar bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSwitchScalar.lean#L33-L60
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSwitchScalar.lean#L33-L60

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightSwitchScalar
set_option autoImplicit false
open ThreeSum ThreeSum.LightSwitchScalar
open Light
set_option maxHeartbeats 1600000

theorem ThreeSum.LightSwitchScalar.scalar_bound {B : ℕ} (hB : 2 ≤ B) (σ : State)
    (hvars : ∀ i, |σ.loc i| ≤ (B : ℤ)) (e : Expr) (he : Small B e) :
    |e.val σ| ≤ ((B^e.cost : ℕ) : ℤ) := by sorry
