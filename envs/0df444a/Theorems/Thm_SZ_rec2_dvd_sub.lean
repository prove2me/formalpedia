-- Prove2me | Theorems.Thm_SZ_rec2_dvd_sub
-- name    : SZ.rec2_dvd_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:42:09.196524+00:00
-- url     : https://prove2.me/theorems/c06d4dfd-26a3-4a5b-9cbf-f3b72573b241
-- title:
--   SZ: rec2 dvd sub
-- statement:
--   **The alternating pattern.**  If `m ∣ A` and `m ∣ B - 1` then the recurrence is
--   `t (n+2) ≡ t n (mod m)`, so the sequence alternates between its two seeds modulo `m`.
--
--   For a quadratic `x² - a x - b` (so `A = a`, `B = b`) this is `a ≡ 0`, `b ≡ 1 (mod m)`; at
--   `m = 2` it says `(x+1)² ∣ x² - a x - b` in `𝔽₂[x]`, the lattice criterion of
--   `plans/plan-dubD1.html` §1.2.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Trace.lean#L103-L120
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Trace.lean#L103-L120

import Definitions.Def_SZ_Defs
import Mathlib.Tactic.LinearCombination
import Definitions.Def_SZ_Trace
set_option autoImplicit false
open SZ

theorem SZ.rec2_dvd_sub {m A B t₀ t₁ : ℤ} (hA : m ∣ A) (hB : m ∣ (B - 1)) (n : ℕ) :
    m ∣ (rec2 A B t₀ t₁ n - if n % 2 = 0 then t₀ else t₁) := by sorry
