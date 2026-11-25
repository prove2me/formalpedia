-- Prove2me | Theorems.Thm_SZ_digitReal_nonneg
-- name    : SZ.digitReal_nonneg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:04:13.470604+00:00
-- url     : https://prove2.me/theorems/f6d0751d-f9e6-4a09-84f4-46245564c539
-- title:
--   SZ: digit Real nonneg
-- statement:
--   The SZ construction uses the digit Real nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/DigitParity.lean#L142-L143
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/DigitParity.lean#L142-L143

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

theorem SZ.digitReal_nonneg (h : IsDigits m d) : 0 ≤ digitReal m d := by sorry
