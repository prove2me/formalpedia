-- Prove2me | Theorems.Thm_P2M_QuadraticFloor_half_sum_zero_of_even__ebacac1c3808
-- name    : P2M_QuadraticFloor_half_sum_zero_of_even__ebacac1c3808
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:45:04.477794+00:00
-- url     : https://prove2.me/theorems/69d3a1f2-a494-5093-a8aa-07334ddb3ceb
-- title:
--   P2 M Quadratic Floor half sum zero of even  ebacac1c3808: P2 M Quadratic Floor half sum zero of even  ebacac1c3808
-- statement:
--   Lemma 3.1(2).
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/HalfPeriod.lean#L56-L79
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/HalfPeriod.lean#L56-L79

module
public import Definitions.Def_QuadraticFloor_Eta
public import Definitions.Def_QuadraticFloor_HalfPeriod
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset

theorem P2M_QuadraticFloor_half_sum_zero_of_even__ebacac1c3808 (f : ℕ → ℂ) {h : ℕ} (hf : ∀ x, f (x + h) = -f x) (h0 : f 0 = 0)
    (hrefl : ∀ x ≤ 2 * h, f (2 * h - x) = f x) : ∑ x ∈ Icc 1 h, f x = 0 := by sorry

alias «QuadraticFloor».«half_sum_zero_of_even'» := P2M_QuadraticFloor_half_sum_zero_of_even__ebacac1c3808
