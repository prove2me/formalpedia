-- Prove2me | Theorems.Thm_P2M_QuadraticFloor_half_sum_zero_of_periodic__7707a5ec64ba
-- name    : P2M_QuadraticFloor_half_sum_zero_of_periodic__7707a5ec64ba
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:44:53.116445+00:00
-- url     : https://prove2.me/theorems/7564488b-4d96-5f1b-afae-19a08c87e2dd
-- title:
--   P2 M Quadratic Floor half sum zero of periodic  7707a5ec64ba: P2 M Quadratic Floor half sum zero of periodic  7707a5ec64ba
-- statement:
--   Lemma 3.1(1).
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/HalfPeriod.lean#L45-L53
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/HalfPeriod.lean#L45-L53

module
public import Definitions.Def_QuadraticFloor_Eta
public import Definitions.Def_QuadraticFloor_HalfPeriod
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset

theorem P2M_QuadraticFloor_half_sum_zero_of_periodic__7707a5ec64ba (f : ℕ → ℂ) {h : ℕ} (hf : ∀ x, f (x + h) = f x)
    (hfull : ∑ x ∈ Icc 1 (2 * h), f x = 0) : ∑ x ∈ Icc 1 h, f x = 0 := by sorry

alias «QuadraticFloor».«half_sum_zero_of_periodic'» := P2M_QuadraticFloor_half_sum_zero_of_periodic__7707a5ec64ba
