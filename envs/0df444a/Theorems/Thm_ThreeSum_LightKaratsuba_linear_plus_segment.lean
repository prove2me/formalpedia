-- Prove2me | Theorems.Thm_ThreeSum_LightKaratsuba_linear_plus_segment
-- name    : ThreeSum.LightKaratsuba.linear_plus_segment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:13:08.020197+00:00
-- url     : https://prove2.me/theorems/dbd45612-8c1a-4415-8268-c907f91dd01b
-- title:
--   Light Karatsuba: linear plus segment
-- statement:
--   The Light Karatsuba construction uses the linear plus segment property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightKaratsuba.lean#L408-L416
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightKaratsuba.lean#L408-L416

import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightKaratsuba
import Theorems.Thm_ThreeSum_Karatsuba_CoeffBound_plus

set_option autoImplicit false
open ThreeSum ThreeSum.LightKaratsuba
open Light
open ThreeSum.Karatsuba
open Polynomial

theorem ThreeSum.LightKaratsuba.linear_plus_segment {μ μ' : ℕ → ℤ} {a b out n : ℕ} {as bs : List ℤ}
    (ha : Seg μ a as) (hb : Seg μ b bs) (hAlen : as.length = n) (hBlen : bs.length = n)
    (hwrite : ∀ i < n, μ' (out + i) = μ (a + i) + 1 * μ (b + i)) :
    Seg μ' out (plus as bs) := by sorry
