-- Prove2me | Theorems.Thm_P2M_BandParity_bandSum_im_modEq_coords__b7058f26c914
-- name    : P2M_BandParity_bandSum_im_modEq_coords__b7058f26c914
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:08:31.480363+00:00
-- url     : https://prove2.me/theorems/de173b60-02e7-42fd-ac99-70386872c26c
-- title:
--   P2 M Band Parity band Sum im mod Eq coords  b7058f26c914: P2 M Band Parity band Sum im mod Eq coords  b7058f26c914
-- statement:
--   **Coordinate Congruence, first form.** `e ≡ Q + k + t (mod 4)`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L363-L379
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L363-L379

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

theorem P2M_BandParity_bandSum_im_modEq_coords__b7058f26c914 (hp8 : p % 8 = 5) (hp5 : 5 < p) (hpin : χ 2 = gi) :
    (bandSum χ).im ≡ Q p + k χ + t χ [ZMOD 4] := by sorry

alias «BandParity».«bandSum_im_modEq_coords'» := P2M_BandParity_bandSum_im_modEq_coords__b7058f26c914
