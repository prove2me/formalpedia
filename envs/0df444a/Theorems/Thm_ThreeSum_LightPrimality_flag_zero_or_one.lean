-- Prove2me | Theorems.Thm_ThreeSum_LightPrimality_flag_zero_or_one
-- name    : ThreeSum.LightPrimality.flag_zero_or_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:03:04.270137+00:00
-- url     : https://prove2.me/theorems/caffd5b2-d0bd-404d-978b-3e15380c969f
-- title:
--   Light Primality: flag zero or one
-- statement:
--   The Light Primality construction uses the flag zero or one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimality.lean#L23-L30
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimality.lean#L23-L30

import Definitions.Def_Submission_ThreeSum_LightResidues
import Mathlib.Data.Nat.Prime.Basic
import Definitions.Def_Submission_ThreeSum_LightPrimality
set_option autoImplicit false
open ThreeSum ThreeSum.LightPrimality
open Light LightResidues
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem ThreeSum.LightPrimality.flag_zero_or_one (n i : ℕ) : flag n i = 0 ∨ flag n i = 1 := by sorry
