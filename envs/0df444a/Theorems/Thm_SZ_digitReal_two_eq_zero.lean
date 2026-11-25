-- Prove2me | Theorems.Thm_SZ_digitReal_two_eq_zero
-- name    : SZ.digitReal_two_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:23:54.732157+00:00
-- url     : https://prove2.me/theorems/19f76638-abaf-40c5-9061-2a4c92776655
-- title:
--   SZ: digit Real two eq zero
-- statement:
--   **`K₂ = {0}`.**  In base `2` the only even digit is `0`, so an even-digit stream
--   represents `0`.  This is the mechanism inside [Dub06EO] Thm 2(i) (`2^{1/q} ∈ 𝒮`), and the
--   reason the construction of this root starts at `m = 3`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/DigitParity.lean#L289-L301
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/DigitParity.lean#L289-L301

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

theorem SZ.digitReal_two_eq_zero {d : ℕ → ℤ} (h : IsDigits 2 d) (hev : ∀ i, Even (d i)) :
    digitReal 2 d = 0 := by sorry
