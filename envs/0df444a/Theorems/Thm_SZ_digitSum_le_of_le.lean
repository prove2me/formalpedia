-- Prove2me | Theorems.Thm_SZ_digitSum_le_of_le
-- name    : SZ.digitSum_le_of_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:03:23.35182+00:00
-- url     : https://prove2.me/theorems/db22d20c-6d11-49a1-a805-d6eec46d46e8
-- title:
--   SZ: digit Sum le of le
-- statement:
--   The **tail estimate**: from index `k` on, a digit stream can add at most `m^{-k}`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/DigitParity.lean#L116-L127
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/DigitParity.lean#L116-L127

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

theorem SZ.digitSum_le_of_le (h : IsDigits m d) {k j : ℕ} (hkj : k ≤ j) :
    digitSum m d j ≤ digitSum m d k + 1 / (m : ℝ) ^ k - 1 / (m : ℝ) ^ j := by sorry
