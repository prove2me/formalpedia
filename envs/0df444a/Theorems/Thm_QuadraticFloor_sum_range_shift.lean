-- Prove2me | Theorems.Thm_QuadraticFloor_sum_range_shift
-- name    : QuadraticFloor.sum_range_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:53:44.493885+00:00
-- url     : https://prove2.me/theorems/a4a3e2fa-fe77-47f8-b400-10b6f25ba618
-- title:
--   Quadratic Floor: sum range shift
-- statement:
--   The Quadratic Floor construction uses the sum range shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Monic.lean#L117-L132
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Monic.lean#L117-L132

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_Monic
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.sum_range_shift {g : ℤ → ℤ} (hg : ∀ m, g (m + p) = g m) (t : ℤ) :
    ∑ n ∈ range p, g (n + t) = ∑ n ∈ range p, g n := by sorry
