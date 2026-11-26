-- Prove2me | Theorems.Thm_QuadraticFloor_sum_range_eq_sum_zmod
-- name    : QuadraticFloor.sum_range_eq_sum_zmod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:43:34.065797+00:00
-- url     : https://prove2.me/theorems/817407c3-1374-5ae2-b814-2c70a7cc30b4
-- title:
--   Quadratic Floor: sum range eq sum zmod
-- statement:
--   A sum over `range p` of a function of the residue is the sum over `ZMod p`.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/RootCount.lean#L52-L59
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/RootCount.lean#L52-L59

module
public import Definitions.Def_QuadraticFloor_Defs
public import Definitions.Def_QuadraticFloor_RootCount
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.sum_range_eq_sum_zmod {M : Type*} [AddCommMonoid M] (G : ZMod p → M) :
    ∑ n ∈ range p, G n = ∑ x : ZMod p, G x := by sorry
