-- Prove2me | Theorems.Thm_ThreeSum_LightKaratsuba_window_sub
-- name    : ThreeSum.LightKaratsuba.window_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:23:45.501054+00:00
-- url     : https://prove2.me/theorems/bae27f46-ecf8-4abd-b159-ac8fe72a0687
-- title:
--   Light Karatsuba: window sub
-- statement:
--   The Light Karatsuba construction uses the window sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightKaratsuba.lean#L319-L323
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightKaratsuba.lean#L319-L323

import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightKaratsuba
set_option autoImplicit false
open ThreeSum ThreeSum.LightKaratsuba
open Light
open ThreeSum.Karatsuba
open Polynomial

theorem ThreeSum.LightKaratsuba.window_sub (f g : ℕ → ℤ) (offset n j : ℕ) :
    window (fun i => f i - g i) offset n j =
      window f offset n j - window g offset n j := by sorry
