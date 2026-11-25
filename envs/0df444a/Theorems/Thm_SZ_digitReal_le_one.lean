-- Prove2me | Theorems.Thm_SZ_digitReal_le_one
-- name    : SZ.digitReal_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:15:16.357287+00:00
-- url     : https://prove2.me/theorems/0c201181-f822-408a-bece-31e52404a143
-- title:
--   SZ: digit Real le one
-- statement:
--   The SZ construction uses the digit Real le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/DigitParity.lean#L145-L146
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/DigitParity.lean#L145-L146

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_DigitParity
set_option autoImplicit false
open SZ
open Finset Filter Topology
variable {m : ℕ} {d : ℕ → ℤ}

theorem SZ.digitReal_le_one (h : IsDigits m d) : digitReal m d ≤ 1 := by sorry
