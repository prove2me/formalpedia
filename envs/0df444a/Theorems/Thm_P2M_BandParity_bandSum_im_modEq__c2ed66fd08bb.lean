-- Prove2me | Theorems.Thm_P2M_BandParity_bandSum_im_modEq__c2ed66fd08bb
-- name    : P2M_BandParity_bandSum_im_modEq__c2ed66fd08bb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:08:13.375938+00:00
-- url     : https://prove2.me/theorems/27362d0d-382e-4e4f-956f-4965f9a1be7b
-- title:
--   P2 M Band Parity band Sum im mod Eq  c2ed66fd08bb: P2 M Band Parity band Sum im mod Eq  c2ed66fd08bb
-- statement:
--   **Theorem A, imaginary part.** `e ≡ κ (mod 4)`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L300-L305
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L300-L305

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

theorem P2M_BandParity_bandSum_im_modEq__c2ed66fd08bb (hp8 : p % 8 = 5) (hpin : χ 2 = gi) :
    (bandSum χ).im ≡ kappa p [ZMOD 4] := by sorry

alias «BandParity».«bandSum_im_modEq'» := P2M_BandParity_bandSum_im_modEq__c2ed66fd08bb
