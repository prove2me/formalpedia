-- Prove2me | Theorems.Thm_ThreeSum_LightPolynomialCoefficient_raw_succ
-- name    : ThreeSum.LightPolynomialCoefficient.raw_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:03:07.722149+00:00
-- url     : https://prove2.me/theorems/ea85d390-9f91-4f8a-9cb6-b4f138bd57e9
-- title:
--   Light Polynomial Coefficient: raw succ
-- statement:
--   The Light Polynomial Coefficient construction uses the raw succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPolynomialCoefficient.lean#L21-L23
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPolynomialCoefficient.lean#L21-L23

import Definitions.Def_Submission_ThreeSum_LightRadixDigit
import Definitions.Def_Submission_ThreeSum_LightPolynomialCoefficient
set_option autoImplicit false
open ThreeSum ThreeSum.LightPolynomialCoefficient
open Light Finset
set_option maxHeartbeats 2000000

theorem ThreeSum.LightPolynomialCoefficient.raw_succ (f g : ℕ → ℕ) (j m k : ℕ) :
    rawCoefficient f g (j+1) m k=rawCoefficient f g j m k+term f g m k j := by sorry
