-- Prove2me | Theorems.Thm_ThreeSum_LightPolynomialProductCheck_flag_zero
-- name    : ThreeSum.LightPolynomialProductCheck.flag_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:03:08.611199+00:00
-- url     : https://prove2.me/theorems/ad967933-25fc-4644-a98c-8cf44d88e198
-- title:
--   Light Polynomial Product Check: flag zero
-- statement:
--   The Light Polynomial Product Check construction uses the flag zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPolynomialProductCheck.lean#L26-L27
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPolynomialProductCheck.lean#L26-L27

import Definitions.Def_Submission_ThreeSum_LightPolynomialCoefficient
import Definitions.Def_Submission_ThreeSum_LightPolynomialProductCheck
set_option autoImplicit false
open ThreeSum ThreeSum.LightPolynomialProductCheck
open Light
set_option maxHeartbeats 2000000
attribute [local instance] ThreeSum.LightPolynomialProductCheck._p2m_local_instance_3bb6a27167_6

theorem ThreeSum.LightPolynomialProductCheck.flag_zero (p : ℕ) (f g expected : ℕ → ℕ) (n m : ℕ) :
    flag p f g expected n m 0=1 := by sorry
