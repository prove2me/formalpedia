-- Prove2me | Theorems.Thm_SZ_exists_digitA_eq_zero
-- name    : SZ.exists_digitA_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:28:12.909541+00:00
-- url     : https://prove2.me/theorems/28a9aa3f-3342-47b0-afca-15b8c76372ab
-- title:
--   SZ: exists digit A eq zero
-- statement:
--   **L1(a)** (note M1 §1.3).  `aₖ = 2` exactly on `A = A₁ ∪ A₂` with `A₁ = (U, 2√3)`,
--   `A₂ = (2√3+U, 3U]`.  `A₁` is absorbing inside `A` (its image misses `A₂`), so an infinite
--   stay in `A` is eventually confined to a single component; the fixed points `3` (of `A₁`)
--   and `3 + 3√3` (of `A₂`) are excluded by `W_ne_three` and `W_ne_top`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L391-L441
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L391-L441

import Definitions.Def_SZ_DigitParity
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_CoverGame
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.exists_digitA_eq_zero (N : ℕ) : ∃ k, N ≤ k ∧ digitA k = 0 := by sorry
