-- Prove2me | Theorems.Thm_ThreeSum_KaratsubaInterface_rounded_word_bound
-- name    : ThreeSum.KaratsubaInterface.rounded_word_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:48:42.290135+00:00
-- url     : https://prove2.me/theorems/05d16f88-42cb-409b-861e-ab25b362ccf4
-- title:
--   Karatsuba Interface: rounded word bound
-- statement:
--   The Karatsuba Interface construction uses the rounded word bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/KaratsubaInterface.lean#L70-L77
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/KaratsubaInterface.lean#L70-L77

import Definitions.Def_Submission_ThreeSum_LightKaratsuba
import Mathlib.Data.Nat.Log
import Definitions.Def_Submission_ThreeSum_KaratsubaInterface
set_option autoImplicit false
open ThreeSum ThreeSum.KaratsubaInterface
open ThreeSum.Karatsuba ThreeSum.LightKaratsuba Polynomial

theorem ThreeSum.KaratsubaInterface.rounded_word_bound {p : ℕ} (hp : 0 < p) (U : ℕ) :
    wordBound (capacity p) U ≤ 1024 * p ^ 3 * (U + 1) ^ 2 := by sorry
