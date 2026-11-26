-- Prove2me | Theorems.Thm_P2M_BandParity_coordinate_congruence__0113bd6e318a
-- name    : P2M_BandParity_coordinate_congruence__0113bd6e318a
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:09:07.410864+00:00
-- url     : https://prove2.me/theorems/56417434-fa7f-4282-bf39-fe57ec37222b
-- title:
--   P2 M Band Parity coordinate congruence  0113bd6e318a: P2 M Band Parity coordinate congruence  0113bd6e318a
-- statement:
--   **Coordinate Congruence.** `κ ≡ Q + k + t (mod 4)`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L382-L384
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L382-L384

module
public import Definitions.Def_BandParity_Laws
public import Definitions.Def_BandParity_Main
set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ

theorem P2M_BandParity_coordinate_congruence__0113bd6e318a (hp8 : p % 8 = 5) (hp5 : 5 < p) (hpin : χ 2 = gi) :
    kappa p ≡ Q p + k χ + t χ [ZMOD 4] := by sorry

alias «BandParity».«coordinate_congruence'» := P2M_BandParity_coordinate_congruence__0113bd6e318a
