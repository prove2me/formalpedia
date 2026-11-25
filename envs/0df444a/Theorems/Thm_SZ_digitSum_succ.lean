-- Prove2me | Theorems.Thm_SZ_digitSum_succ
-- name    : SZ.digitSum_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:38:58.225578+00:00
-- url     : https://prove2.me/theorems/3136acda-6627-4a7b-bb62-539edfdab848
-- title:
--   SZ: digit Sum succ
-- statement:
--   The SZ construction uses the digit Sum succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/DigitParity.lean#L101-L103
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/DigitParity.lean#L101-L103

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

theorem SZ.digitSum_succ (m : ℕ) (d : ℕ → ℤ) (k : ℕ) :
    digitSum m d (k + 1) = digitSum m d k + (d k : ℝ) / (m : ℝ) ^ (k + 1) := by sorry
