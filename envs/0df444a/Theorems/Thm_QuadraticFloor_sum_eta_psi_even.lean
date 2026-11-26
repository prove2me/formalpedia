-- Prove2me | Theorems.Thm_QuadraticFloor_sum_eta_psi_even
-- name    : QuadraticFloor.sum_eta_psi_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:50:45.191355+00:00
-- url     : https://prove2.me/theorems/44ed4a73-f296-5bd9-ae4f-f9a543b64936
-- title:
--   Quadratic Floor: sum eta psi even
-- statement:
--   An even, anti-periodic product `η_p ψ c` has vanishing half sum (Lemma 3.1(2)).
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L271-L284
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L271-L284

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

theorem QuadraticFloor.sum_eta_psi_even (hp2 : p ≠ 2) (hA : Odd A) (ψ : DirichletCharacter ℂ A) (c : ℕ → ℂ)
    (s : ℂ) (hcper : ∀ x, c (x + 4 * A * p) = c x)
    (hcref : ∀ x ≤ 8 * A * p, c (8 * A * p - x) = s * c x) (hs : s * ψ (-1) = -1) :
    ∑ x ∈ Icc 1 (4 * A * p), (eta p x : ℂ) * ψ (x : ZMod A) * c x = 0 := by sorry
