-- Prove2me | Theorems.Thm_SZ_digitSum_le_digitReal
-- name    : SZ.digitSum_le_digitReal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:39:08.258928+00:00
-- url     : https://prove2.me/theorems/ec3ce998-5369-457a-a5c6-833895e73c94
-- title:
--   SZ: digit Sum le digit Real
-- statement:
--   The SZ construction uses the digit Sum le digit Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/DigitParity.lean#L138-L140
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/DigitParity.lean#L138-L140

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

theorem SZ.digitSum_le_digitReal (h : IsDigits m d) (k : ℕ) :
    digitSum m d k ≤ digitReal m d := by sorry
