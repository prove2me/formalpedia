-- Prove2me | Theorems.Thm_QuadraticFloor_sum_mul_legendre_eq_zero
-- name    : QuadraticFloor.sum_mul_legendre_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:49:32.905386+00:00
-- url     : https://prove2.me/theorems/d76b886f-3337-44c7-97a6-1396d2cb8dac
-- title:
--   Quadratic Floor: sum mul legendre eq zero
-- statement:
--   A periodic function times the Legendre symbol sums to zero over a full period.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/HalfPeriod.lean#L90-L128
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/HalfPeriod.lean#L90-L128

module
public import Definitions.Def_QuadraticFloor_Eta
public import Definitions.Def_QuadraticFloor_HalfPeriod
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.sum_mul_legendre_eq_zero (hp2 : p ≠ 2) (g : ℕ → ℂ) {m : ℕ} (hm : ¬ p ∣ m)
    (hg : ∀ x, g (x + m) = g x) :
    ∑ x ∈ Icc 1 (m * p), g x * (legendreSym p x : ℂ) = 0 := by sorry
