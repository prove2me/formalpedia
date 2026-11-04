-- Prove2me | Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_congr
-- name    : ThreeSum.LightKaratsuba.ProductAt.congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:24:07.351047+00:00
-- url     : https://prove2.me/theorems/b28cdfd3-513d-4101-97cd-34e8228e9381
-- title:
--   Product At: congr
-- statement:
--   The Product At construction uses the congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightKaratsuba.lean#L426-L429
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightKaratsuba.lean#L426-L429

import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightKaratsuba
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Seg_congr

set_option autoImplicit false
open ThreeSum ThreeSum.LightKaratsuba
open Light
open ThreeSum.Karatsuba
open Polynomial

theorem ThreeSum.LightKaratsuba.ProductAt.congr {μ μ' : ℕ → ℤ} {out n : ℕ} {as bs : List ℤ}
    (hp : ProductAt μ out n as bs)
    (he : ∀ j < 2 * n, μ' (out + j) = μ (out + j)) :
    ProductAt μ' out n as bs := by sorry
