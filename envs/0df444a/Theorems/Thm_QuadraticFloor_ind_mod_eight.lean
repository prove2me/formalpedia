-- Prove2me | Theorems.Thm_QuadraticFloor_ind_mod_eight
-- name    : QuadraticFloor.ind_mod_eight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:50:35.991981+00:00
-- url     : https://prove2.me/theorems/ce024ea8-3f18-4dd9-9c2b-1a65f1f16940
-- title:
--   Quadratic Floor: ind mod eight
-- statement:
--   The indicator of `x ≡ d (mod 8)` for odd `x` and `d ≡ 1 (mod 4)`.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L93-L105
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L93-L105

module
public import Definitions.Def_QuadraticFloor_HalfPeriod
public import Definitions.Def_QuadraticFloor_SquareClass
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset

theorem QuadraticFloor.ind_mod_eight {x d : ℕ} (hx : Odd x) (hd : d % 4 = 1) :
    (if x % 8 = d % 8 then (1 : ℂ) else 0) = (1 / 4) * (1 + (ZMod.χ₄ (x : ZMod 4) : ℂ) +
      (ZMod.χ₈ (d : ZMod 8) : ℂ) * ((ZMod.χ₈ (x : ZMod 8) : ℂ) + (ZMod.χ₈' (x : ZMod 8) : ℂ))) := by sorry
