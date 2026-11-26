-- Prove2me | Theorems.Thm_P2M_QuadraticFloor_bern_antiperiodic__37acfbc76d79
-- name    : P2M_QuadraticFloor_bern_antiperiodic__37acfbc76d79
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:45:12.121335+00:00
-- url     : https://prove2.me/theorems/39e3f869-aa96-48d6-97ff-d7c641946b1e
-- title:
--   P2 M Quadratic Floor bern antiperiodic  37acfbc76d79: P2 M Quadratic Floor bern antiperiodic  37acfbc76d79
-- statement:
--   Lemma 3.1(3).
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/HalfPeriod.lean#L29-L42
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/HalfPeriod.lean#L29-L42

module
public import Definitions.Def_QuadraticFloor_Eta
public import Definitions.Def_QuadraticFloor_HalfPeriod
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset

theorem P2M_QuadraticFloor_bern_antiperiodic__37acfbc76d79 (f : ℕ → ℂ) {h : ℕ} (hh : 0 < h) (hf : ∀ x, f (x + h) = -f x) :
    bern (2 * h) f = -(1 / 2) * ∑ x ∈ Icc 1 h, f x := by sorry

alias «QuadraticFloor».«bern_antiperiodic'» := P2M_QuadraticFloor_bern_antiperiodic__37acfbc76d79
