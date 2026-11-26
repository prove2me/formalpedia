-- Prove2me | Theorems.Thm_QuadraticFloor_bern_antiperiodic
-- name    : QuadraticFloor.bern_antiperiodic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:02:20.973985+00:00
-- url     : https://prove2.me/theorems/cdb07292-1232-55fc-9764-896c3e205408
-- title:
--   Quadratic Floor: bern antiperiodic
-- statement:
--   **Lemma 3.1(3).** If `f(x + h) = -f(x)`, then `B_{1,f}^{(2h)} = -(1/2) ∑_{x=1}^{h} f(x)`.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/Solution.lean#L59-L61
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/Solution.lean#L59-L61

module
public import Definitions.Def_QuadraticFloor
public import Definitions.Def_QuadraticFloor_Solution
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.bern_antiperiodic (f : ℕ → ℂ) {h : ℕ} (hh : 0 < h) (hf : ∀ x, f (x + h) = -f x) :
    bern (2 * h) f = -(1 / 2) * ∑ x ∈ Icc 1 h, f x := by sorry
