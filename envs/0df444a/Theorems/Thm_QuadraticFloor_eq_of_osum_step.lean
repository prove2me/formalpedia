-- Prove2me | Theorems.Thm_QuadraticFloor_eq_of_osum_step
-- name    : QuadraticFloor.eq_of_osum_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:46:41.936538+00:00
-- url     : https://prove2.me/theorems/418f2556-1583-5834-b053-967fbed45e3c
-- title:
--   Quadratic Floor: eq of osum step
-- statement:
--   Two functions related by a constant step have oriented sums related in the same way.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Monic.lean#L47-L57
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Monic.lean#L47-L57

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_Monic
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset

theorem QuadraticFloor.eq_of_osum_step {F : ℤ → ℤ} {g : ℤ → ℤ} (hF : ∀ c, F (c + 1) = F c + g c) (c : ℤ) :
    F c = F 0 + osum c g := by sorry
