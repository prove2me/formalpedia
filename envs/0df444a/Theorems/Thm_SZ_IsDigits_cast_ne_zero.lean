-- Prove2me | Theorems.Thm_SZ_IsDigits_cast_ne_zero
-- name    : SZ.IsDigits.cast_ne_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:03:23.84131+00:00
-- url     : https://prove2.me/theorems/d6f63084-8448-4ccb-8fbc-7b8123113bff
-- title:
--   Is Digits: cast ne zero
-- statement:
--   The Is Digits construction uses the cast ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/DigitParity.lean#L84-L84
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/DigitParity.lean#L84-L84

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
open SZ.IsDigits
variable {m : ℕ} {d : ℕ → ℤ}

theorem SZ.IsDigits.cast_ne_zero (h : IsDigits m d) : (m : ℝ) ≠ 0 := by sorry
