-- Prove2me | Theorems.Thm_ThreeSum_KaratsubaInterface_rounded_time_fifth_power
-- name    : ThreeSum.KaratsubaInterface.rounded_time_fifth_power
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:31:01.186793+00:00
-- url     : https://prove2.me/theorems/e20880f5-fd50-4101-9dde-c715dccb4c03
-- title:
--   Karatsuba Interface: rounded time fifth power
-- statement:
--   The exact exponent certificate for length `p`: time to the fifth power
--   is bounded by a fixed constant times `p^8`, including linear overhead.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/KaratsubaInterface.lean#L60-L68
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/KaratsubaInterface.lean#L60-L68

import Definitions.Def_Submission_ThreeSum_LightKaratsuba
import Mathlib.Data.Nat.Log
import Definitions.Def_Submission_ThreeSum_KaratsubaInterface
set_option autoImplicit false
open ThreeSum ThreeSum.KaratsubaInterface
open ThreeSum.Karatsuba ThreeSum.LightKaratsuba Polynomial

theorem ThreeSum.KaratsubaInterface.rounded_time_fifth_power {p : ℕ} (hp : 0 < p) (c : ℕ) :
    (time (Nat.clog 2 p) + c * capacity p + c) ^ 5 ≤
      ((2530 + 2 * c) ^ 5 * 2 ^ 8) * p ^ 8 := by sorry
