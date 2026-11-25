-- Prove2me | Theorems.Thm_SZ_exists_digitB_eq_two
-- name    : SZ.exists_digitB_eq_two
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:28:04.934946+00:00
-- url     : https://prove2.me/theorems/bb7b58d6-2a54-4bbc-86de-078047ecf396
-- title:
--   SZ: exists digit B eq two
-- statement:
--   **L1(b)** (note M1 §1.4).  Under the selection rule of `pick`, `bₖ = 0` exactly on
--   `L = [0, 2√3)`.  Were `bₖ = 0` from some point on, the state would be confined to
--   `[0, 2√3/3) ∪ (U, 2 + 2√3/3)`; the second zone is absorbing and carries the expanding map
--   `w ↦ 3w - 6` with fixed point `3`, excluded by `W_ne_three`, while on the first zone the
--   state is multiplied by `3` forever, contradicting `W_pos`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L316-L383
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L316-L383

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

theorem SZ.exists_digitB_eq_two (N : ℕ) : ∃ k, N ≤ k ∧ digitB k = 2 := by sorry
