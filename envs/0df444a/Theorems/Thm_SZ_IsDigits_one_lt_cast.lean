-- Prove2me | Theorems.Thm_SZ_IsDigits_one_lt_cast
-- name    : SZ.IsDigits.one_lt_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:39:05.674014+00:00
-- url     : https://prove2.me/theorems/372c09a3-078f-4735-b524-764fc70f2b05
-- title:
--   Is Digits: one lt cast
-- statement:
--   The Is Digits construction uses the one lt cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/DigitParity.lean#L79-L80
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/DigitParity.lean#L79-L80

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

theorem SZ.IsDigits.one_lt_cast (h : IsDigits m d) : (1 : ℝ) < (m : ℝ) := by sorry
