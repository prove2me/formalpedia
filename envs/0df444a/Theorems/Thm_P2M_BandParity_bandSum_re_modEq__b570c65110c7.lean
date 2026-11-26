-- Prove2me | Theorems.Thm_P2M_BandParity_bandSum_re_modEq__b570c65110c7
-- name    : P2M_BandParity_bandSum_re_modEq__b570c65110c7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:08:23.610182+00:00
-- url     : https://prove2.me/theorems/4a3057e8-ce38-5daa-a038-498857ff755f
-- title:
--   P2 M Band Parity band Sum re mod Eq  b570c65110c7: P2 M Band Parity band Sum re mod Eq  b570c65110c7
-- statement:
--   **Theorem A, real part.** `f ≡ Q (mod 4)`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L288-L297
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L288-L297

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

theorem P2M_BandParity_bandSum_re_modEq__b570c65110c7 (hp8 : p % 8 = 5) :
    (bandSum χ).re ≡ Q p [ZMOD 4] := by sorry

alias «BandParity».«bandSum_re_modEq'» := P2M_BandParity_bandSum_re_modEq__b570c65110c7
