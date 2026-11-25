-- Prove2me | Theorems.Thm_SZ_not_isSquare_of_bounded
-- name    : SZ.not_isSquare_of_bounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:43:47.098875+00:00
-- url     : https://prove2.me/theorems/08dcc92e-f0e1-4b79-8a00-a05959d21823
-- title:
--   SZ: not is Square of bounded
-- statement:
--   `Nat.sqrt` does not reduce in the kernel, so the `DecidablePred (IsSquare : ℕ → Prop)`
--   instance is useless to `decide`; this reduces the check to a bounded search, which
--   `decide` does handle.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L78-L85
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L78-L85

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_DigitParity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Definitions.Def_SZ_Slice
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.not_isSquare_of_bounded {n : ℕ} (hn : 0 < n) (h : ∀ r, r ≤ n → r * r ≠ n) :
    ¬ IsSquare n := by sorry
