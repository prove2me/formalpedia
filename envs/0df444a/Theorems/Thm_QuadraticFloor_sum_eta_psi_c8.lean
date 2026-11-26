-- Prove2me | Theorems.Thm_QuadraticFloor_sum_eta_psi_c8
-- name    : QuadraticFloor.sum_eta_psi_c8
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:50:44.288394+00:00
-- url     : https://prove2.me/theorems/30e974f1-cffd-4fc7-b7fb-53de60d0553f
-- title:
--   Quadratic Floor: sum eta psi c8
-- statement:
--   Terms with `χ_{±8}` are periodic under `x ↦ x + 4Ap` and vanish (Lemma 3.1(1)).
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L249-L268
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L249-L268

module
public import Definitions.Def_QuadraticFloor_HalfPeriod
public import Definitions.Def_QuadraticFloor_SquareClass
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {A : ℕ}

theorem QuadraticFloor.sum_eta_psi_c8 (hp2 : p ≠ 2) (hA : Odd A) (hpA : ¬ p ∣ A) (ψ : DirichletCharacter ℂ A)
    (c : ZMod 8 → ℂ) (hc : ∀ y, c (y + 4) = -c y) :
    ∑ x ∈ Icc 1 (4 * A * p), (eta p x : ℂ) * ψ (x : ZMod A) * c (x : ZMod 8) = 0 := by sorry
