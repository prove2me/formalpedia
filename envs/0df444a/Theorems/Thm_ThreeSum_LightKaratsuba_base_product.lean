-- Prove2me | Theorems.Thm_ThreeSum_LightKaratsuba_base_product
-- name    : ThreeSum.LightKaratsuba.base_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:11:49.186085+00:00
-- url     : https://prove2.me/theorems/ab71256b-e405-419d-a9e6-e4c47fd6d94f
-- title:
--   Light Karatsuba: base product
-- statement:
--   The Light Karatsuba construction uses the base product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightKaratsuba.lean#L298-L315
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightKaratsuba.lean#L298-L315

import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightKaratsuba
set_option autoImplicit false
open ThreeSum ThreeSum.LightKaratsuba
open Light
open ThreeSum.Karatsuba
open Polynomial
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightKaratsuba.base_product {μ μ' : ℕ → ℤ} {a b out : ℕ} {as bs : List ℤ}
    (ha : Seg μ a as) (hb : Seg μ b bs)
    (hAlen : as.length = 1) (hBlen : bs.length = 1)
    (hzero : μ' out = μ a * μ b) (hone : μ' (out + 1) = 0) :
    ProductAt μ' out 1 as bs := by sorry
