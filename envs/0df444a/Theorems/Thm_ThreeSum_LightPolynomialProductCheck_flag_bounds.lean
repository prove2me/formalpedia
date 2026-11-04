-- Prove2me | Theorems.Thm_ThreeSum_LightPolynomialProductCheck_flag_bounds
-- name    : ThreeSum.LightPolynomialProductCheck.flag_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:03:09.012204+00:00
-- url     : https://prove2.me/theorems/3e032f2e-7d94-4624-a40c-d638529947f1
-- title:
--   Light Polynomial Product Check: flag bounds
-- statement:
--   The Light Polynomial Product Check construction uses the flag bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPolynomialProductCheck.lean#L29-L32
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPolynomialProductCheck.lean#L29-L32

import Definitions.Def_Submission_ThreeSum_LightPolynomialCoefficient
import Definitions.Def_Submission_ThreeSum_LightPolynomialProductCheck
set_option autoImplicit false
open ThreeSum ThreeSum.LightPolynomialProductCheck
open Light
set_option maxHeartbeats 2000000
attribute [local instance] ThreeSum.LightPolynomialProductCheck._p2m_local_instance_3bb6a27167_6

theorem ThreeSum.LightPolynomialProductCheck.flag_bounds (p : ℕ) (f g expected : ℕ → ℕ) (n m len : ℕ) :
    0≤flag p f g expected n m len ∧ flag p f g expected n m len≤1 := by sorry
