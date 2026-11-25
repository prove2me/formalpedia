-- Prove2me | Theorems.Thm_SZ_dvd_floor_add_digitReal_mul_pow
-- name    : SZ.dvd_floor_add_digitReal_mul_pow
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:15:01.456814+00:00
-- url     : https://prove2.me/theorems/6cc39a43-0fc8-4c86-9f4b-5f3e441c1982
-- title:
--   SZ: dvd floor add digit Real mul pow
-- statement:
--   **Lemma D at a general modulus** (paper Lemma 3.1, the *telescoping* lemma).  If
--   `p ∣ N` and `p` divides every digit of `d`, then `p ∣ ⌊(N + digitReal m d) mˢ⌋` for every
--   `s`.  The paper induces on `s` and needs `p ∣ m` or `p ∣ m - 1` to carry the induction;
--   the explicit floor formula above makes both hypotheses unnecessary, since each summand
--   `dᵢ m^{s-1-i}` is divisible by `p` on the nose.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/DigitParity.lean#L228-L232
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/DigitParity.lean#L228-L232

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

theorem SZ.dvd_floor_add_digitReal_mul_pow (h : IsDigits m d) {p N : ℤ} (hN : p ∣ N)
    (hdvd : ∀ i, p ∣ d i) (s : ℕ) {i₀ : ℕ} (hk : s ≤ i₀) (hsmall : d i₀ ≤ (m : ℤ) - 2) :
    p ∣ ⌊((N : ℝ) + digitReal m d) * (m : ℝ) ^ s⌋ := by sorry
