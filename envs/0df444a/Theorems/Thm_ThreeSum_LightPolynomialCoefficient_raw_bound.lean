-- Prove2me | Theorems.Thm_ThreeSum_LightPolynomialCoefficient_raw_bound
-- name    : ThreeSum.LightPolynomialCoefficient.raw_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:05:11.626755+00:00
-- url     : https://prove2.me/theorems/693ae777-8f14-4918-929f-fe0f4bb56038
-- title:
--   Light Polynomial Coefficient: raw bound
-- statement:
--   The Light Polynomial Coefficient construction uses the raw bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPolynomialCoefficient.lean#L25-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPolynomialCoefficient.lean#L25-L39

import Definitions.Def_Submission_ThreeSum_LightRadixDigit
import Definitions.Def_Submission_ThreeSum_LightPolynomialCoefficient
set_option autoImplicit false
open ThreeSum ThreeSum.LightPolynomialCoefficient
open Light Finset
set_option maxHeartbeats 2000000

theorem ThreeSum.LightPolynomialCoefficient.raw_bound (f g : ℕ → ℕ) {n m k j p : ℕ}
    (hf : ∀ i<n, f i<p) (hg : ∀ i<m, g i<p) (hj : j≤n) :
    rawCoefficient f g j m k≤j*p^2 := by sorry
