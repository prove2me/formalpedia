-- Prove2me | Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_bound
-- name    : ThreeSum.LightKaratsuba.ProductAt.bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:24:08.055112+00:00
-- url     : https://prove2.me/theorems/f4410315-4e3c-4603-9c85-8e2a4d41c59f
-- title:
--   Product At: bound
-- statement:
--   The Product At construction uses the bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightKaratsuba.lean#L418-L424
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightKaratsuba.lean#L418-L424

import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightKaratsuba
set_option autoImplicit false
open ThreeSum ThreeSum.LightKaratsuba
open Light
open ThreeSum.Karatsuba
open Polynomial

theorem ThreeSum.LightKaratsuba.ProductAt.bound {μ : ℕ → ℤ} {out n : ℕ} {as bs : List ℤ} {U : ℤ}
    (hp : ProductAt μ out n as bs) (ha : as.length ≤ n) (hb : bs.length ≤ n)
    (hA : CoeffBound as U) (hB : CoeffBound bs U) :
    ∀ j < 2 * n, |μ (out + j)| ≤ 2 * (n : ℤ) * U ^ 2 := by sorry
