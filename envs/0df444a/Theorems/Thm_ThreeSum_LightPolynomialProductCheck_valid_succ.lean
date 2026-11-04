-- Prove2me | Theorems.Thm_ThreeSum_LightPolynomialProductCheck_valid_succ
-- name    : ThreeSum.LightPolynomialProductCheck.valid_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:03:09.660762+00:00
-- url     : https://prove2.me/theorems/8749c696-0f97-46ae-92f8-0c1be1e9de43
-- title:
--   Light Polynomial Product Check: valid succ
-- statement:
--   The Light Polynomial Product Check construction uses the valid succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPolynomialProductCheck.lean#L13-L21
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPolynomialProductCheck.lean#L13-L21

import Definitions.Def_Submission_ThreeSum_LightPolynomialCoefficient
import Definitions.Def_Submission_ThreeSum_LightPolynomialProductCheck
set_option autoImplicit false
open ThreeSum ThreeSum.LightPolynomialProductCheck
open Light
set_option maxHeartbeats 2000000
attribute [local instance] ThreeSum.LightPolynomialProductCheck._p2m_local_instance_3bb6a27167_6

theorem ThreeSum.LightPolynomialProductCheck.valid_succ (p : ℕ) (f g expected : ℕ → ℕ) (n m len : ℕ) :
    Valid p f g expected n m (len+1) ↔
      Valid p f g expected n m len ∧ expected len=coefficient p f g n m len := by sorry
