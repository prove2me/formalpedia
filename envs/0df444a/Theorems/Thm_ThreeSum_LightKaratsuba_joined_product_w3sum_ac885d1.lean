-- Prove2me | Theorems.Thm_ThreeSum_LightKaratsuba_joined_product_w3sum_ac885d1
-- name    : ThreeSum.LightKaratsuba.joined_product_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:12:22.547602+00:00
-- url     : https://prove2.me/theorems/e07e6075-9eac-4e54-a2bf-93eb20bfb7ac
-- title:
--   Light Karatsuba: joined product
-- statement:
--   The coefficient identity matched by the six actual joining passes.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightKaratsuba.lean#L342-L379
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightKaratsuba.lean#L342-L379

import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightKaratsuba
import Theorems.Thm_ThreeSum_Karatsuba_CoeffBound_drop
import Theorems.Thm_ThreeSum_Karatsuba_CoeffBound_plus
import Theorems.Thm_ThreeSum_Karatsuba_CoeffBound_take

set_option autoImplicit false
open ThreeSum ThreeSum.LightKaratsuba
open Light
open ThreeSum.Karatsuba
open Polynomial

theorem ThreeSum.LightKaratsuba.joined_product_w3sum_ac885d1 {μ : ℕ → ℤ} {work n half : ℕ} {as bs : List ℤ}
    (hhalf : 2 * half = n) (ha : as.length = n) (hb : bs.length = n)
    (h0 : ProductAt μ work half (as.take half) (bs.take half))
    (h2 : ProductAt μ (work + n) half (as.drop half) (bs.drop half))
    (hm : ProductAt μ (work + 2 * n) half
      (plus (as.take half) (as.drop half)) (plus (bs.take half) (bs.drop half)))
    (j : ℕ) : joined μ work n half j = (asPolynomial as * asPolynomial bs).coeff j := by sorry
