-- Prove2me | Theorems.Thm_ThreeSum_LightKaratsuba_wordBound_ge_twice
-- name    : ThreeSum.LightKaratsuba.wordBound_ge_twice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:12:24.457229+00:00
-- url     : https://prove2.me/theorems/d26998ad-06d6-498f-9e6c-b3846f7169c4
-- title:
--   Light Karatsuba: word Bound ge twice
-- statement:
--   The Light Karatsuba construction uses the word Bound ge twice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightKaratsuba.lean#L393-L398
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightKaratsuba.lean#L393-L398

import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightKaratsuba
set_option autoImplicit false
open ThreeSum ThreeSum.LightKaratsuba
open Light
open ThreeSum.Karatsuba
open Polynomial

theorem ThreeSum.LightKaratsuba.wordBound_ge_twice (n U : ℕ) (hn : 0 < n) : 2 * U ≤ wordBound n U := by sorry
