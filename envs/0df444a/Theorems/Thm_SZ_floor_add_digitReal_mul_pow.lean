-- Prove2me | Theorems.Thm_SZ_floor_add_digitReal_mul_pow
-- name    : SZ.floor_add_digitReal_mul_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:04:20.272801+00:00
-- url     : https://prove2.me/theorems/06314c50-0287-43f5-82d3-765ce62cda39
-- title:
--   SZ: floor add digit Real mul pow
-- statement:
--   **The floor identity.**  With `N` an integer and `d` a base-`m` digit stream having
--   some digit `≤ m - 2` at an index `≥ s`, the integral part of `(N + digitReal m d) mˢ` is
--   the explicit integer `N mˢ + ∑_{i < s} dᵢ m^{s-1-i}`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/DigitParity.lean#L207-L221
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/DigitParity.lean#L207-L221

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

theorem SZ.floor_add_digitReal_mul_pow (h : IsDigits m d) (N : ℤ) (s : ℕ) {i₀ : ℕ}
    (hk : s ≤ i₀) (hsmall : d i₀ ≤ (m : ℤ) - 2) :
    ⌊((N : ℝ) + digitReal m d) * (m : ℝ) ^ s⌋
      = N * (m : ℤ) ^ s + ∑ i ∈ Finset.range s, d i * (m : ℤ) ^ (s - (i + 1)) := by sorry
