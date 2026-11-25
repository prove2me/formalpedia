-- Prove2me | Theorems.Thm_SZ_bddAbove_digitSum
-- name    : SZ.bddAbove_digitSum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:15:02.385372+00:00
-- url     : https://prove2.me/theorems/7bf30930-573f-4b89-8149-d31c7045c5f9
-- title:
--   SZ: bdd Above digit Sum
-- statement:
--   The SZ construction uses the bdd Above digit Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/DigitParity.lean#L135-L136
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/DigitParity.lean#L135-L136

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

theorem SZ.bddAbove_digitSum (h : IsDigits m d) : BddAbove (Set.range (digitSum m d)) := by sorry
