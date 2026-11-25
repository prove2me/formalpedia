-- Prove2me | Theorems.Thm_SZ_Slice_mem_MahlerZ_of_dvd
-- name    : SZ.Slice.mem_MahlerZ_of_dvd
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:08:23.300526+00:00
-- url     : https://prove2.me/theorems/c24abb80-8b32-4bfa-a695-55d4bbaf55bb
-- title:
--   Slice: mem Mahler Z of dvd
-- statement:
--   At `p = 2` divisibility is parity, so a witness of the reduction places `√m` in `𝒵`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L728-L735
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L728-L735

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
open SZ.Slice
variable (S : Slice)
variable {S}

theorem SZ.Slice.mem_MahlerZ_of_dvd (S : Slice) (hp : S.p = 2)
    (h : ∃ ξ : ℝ, 0 < ξ ∧ ∀ n : ℕ, 1 ≤ n → S.p ∣ ⌊ξ * Real.sqrt S.m ^ n⌋) :
    Real.sqrt S.m ∈ MahlerZ := by sorry
