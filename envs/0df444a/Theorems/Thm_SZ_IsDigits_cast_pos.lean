-- Prove2me | Theorems.Thm_SZ_IsDigits_cast_pos
-- name    : SZ.IsDigits.cast_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:38:59.923245+00:00
-- url     : https://prove2.me/theorems/4e6c5eb2-763a-477e-a100-a0055c0b670f
-- title:
--   Is Digits: cast pos
-- statement:
--   The Is Digits construction uses the cast pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/DigitParity.lean#L82-L82
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/DigitParity.lean#L82-L82

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

theorem SZ.IsDigits.cast_pos (h : IsDigits m d) : (0 : ℝ) < (m : ℝ) := by sorry
