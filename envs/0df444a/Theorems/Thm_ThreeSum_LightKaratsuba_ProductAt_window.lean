-- Prove2me | Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_window
-- name    : ThreeSum.LightKaratsuba.ProductAt.window
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:11:47.18869+00:00
-- url     : https://prove2.me/theorems/f5610607-ced3-40d6-ac92-d4f802bc6bea
-- title:
--   Product At: window
-- statement:
--   The Product At construction uses the window property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightKaratsuba.lean#L325-L339
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightKaratsuba.lean#L325-L339

import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightKaratsuba
set_option autoImplicit false
open ThreeSum ThreeSum.LightKaratsuba
open Light
open ThreeSum.Karatsuba
open Polynomial

theorem ThreeSum.LightKaratsuba.ProductAt.window {μ : ℕ → ℤ} {out n : ℕ} {as bs : List ℤ}
    (hp : ProductAt μ out n as bs) (ha : as.length ≤ n) (hb : bs.length ≤ n)
    (offset j : ℕ) :
    window (fun i => μ (out + i)) offset (2 * n) j =
      (X ^ offset * (asPolynomial as * asPolynomial bs)).coeff j := by sorry
