-- Prove2me | Theorems.Thm_SZ_even_floor_add_digitReal_mul_pow
-- name    : SZ.even_floor_add_digitReal_mul_pow
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:04:26.803399+00:00
-- url     : https://prove2.me/theorems/a1871b6d-4800-43b8-b1ad-9c656c4e73c4
-- title:
--   SZ: even floor add digit Real mul pow
-- statement:
--   **Lemma D, the direction used.**  If `N` is even and every digit of `d` is even, then
--   every `⌊(N + digitReal m d) mˢ⌋` is even — the parity engine of `SZ/SqrtThree.lean`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/DigitParity.lean#L236-L241
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/DigitParity.lean#L236-L241

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

theorem SZ.even_floor_add_digitReal_mul_pow (h : IsDigits m d) {N : ℤ} (hN : Even N)
    (hev : ∀ i, Even (d i)) (s : ℕ) {i₀ : ℕ} (hk : s ≤ i₀) (hsmall : d i₀ ≤ (m : ℤ) - 2) :
    Even ⌊((N : ℝ) + digitReal m d) * (m : ℝ) ^ s⌋ := by sorry
