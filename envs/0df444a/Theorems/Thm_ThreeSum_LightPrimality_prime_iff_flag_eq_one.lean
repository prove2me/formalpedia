-- Prove2me | Theorems.Thm_ThreeSum_LightPrimality_prime_iff_flag_eq_one
-- name    : ThreeSum.LightPrimality.prime_iff_flag_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:18:34.835197+00:00
-- url     : https://prove2.me/theorems/0a07d1bd-d1d5-41d3-8b8d-4b2d5ef8d9b4
-- title:
--   Light Primality: prime iff flag eq one
-- statement:
--   The Light Primality construction uses the prime iff flag eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimality.lean#L53-L63
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimality.lean#L53-L63

import Definitions.Def_Submission_ThreeSum_LightResidues
import Mathlib.Data.Nat.Prime.Basic
import Definitions.Def_Submission_ThreeSum_LightPrimality
set_option autoImplicit false
open ThreeSum ThreeSum.LightPrimality
open Light LightResidues
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem ThreeSum.LightPrimality.prime_iff_flag_eq_one {n : ℕ} (hn : 2 ≤ n) :
    Nat.Prime n ↔ flag n (n-2) = 1 := by sorry
