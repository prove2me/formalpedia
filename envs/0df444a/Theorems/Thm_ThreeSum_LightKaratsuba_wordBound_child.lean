-- Prove2me | Theorems.Thm_ThreeSum_LightKaratsuba_wordBound_child
-- name    : ThreeSum.LightKaratsuba.wordBound_child
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:12:33.501645+00:00
-- url     : https://prove2.me/theorems/924d5391-01f3-46f4-8265-d6a44da90ccd
-- title:
--   Light Karatsuba: word Bound child
-- statement:
--   The Light Karatsuba construction uses the word Bound child property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightKaratsuba.lean#L385-L391
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightKaratsuba.lean#L385-L391

import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightKaratsuba
set_option autoImplicit false
open ThreeSum ThreeSum.LightKaratsuba
open Light
open ThreeSum.Karatsuba
open Polynomial

theorem ThreeSum.LightKaratsuba.wordBound_child (m U : ℕ) : wordBound m (2 * U) ≤ wordBound (2 * m) U := by sorry
