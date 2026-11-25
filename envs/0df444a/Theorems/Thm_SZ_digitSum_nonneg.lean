-- Prove2me | Theorems.Thm_SZ_digitSum_nonneg
-- name    : SZ.digitSum_nonneg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:40:19.981518+00:00
-- url     : https://prove2.me/theorems/7ba0a425-e794-4d71-984a-2a8ecfd91591
-- title:
--   SZ: digit Sum nonneg
-- statement:
--   The SZ construction uses the digit Sum nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/DigitParity.lean#L112-L113
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/DigitParity.lean#L112-L113

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

theorem SZ.digitSum_nonneg (h : IsDigits m d) (k : ℕ) : 0 ≤ digitSum m d k := by sorry
