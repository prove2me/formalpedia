-- Prove2me | Theorems.Thm_P2M_BandParity_lag_identity__1cd92334e44b
-- name    : P2M_BandParity_lag_identity__1cd92334e44b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:07:32.441918+00:00
-- url     : https://prove2.me/theorems/78727b06-aeaa-4993-91f2-2ebc0c21ce7b
-- title:
--   P2 M Band Parity lag identity  1cd92334e44b: P2 M Band Parity lag identity  1cd92334e44b
-- statement:
--   **The lag identity.** Matching `2H` with `4H = -H` by multiplication by `2` has correlation
--   exactly `κ`: `∑_{u ∈ 2H} s(u) s(2u) = κ`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L212-L283
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L212-L283

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

theorem P2M_BandParity_lag_identity__1cd92334e44b (hp8 : p % 8 = 5) :
    ∑ u ∈ cls χ gi, parSign u * parSign (2 * u) = kappa p := by sorry

alias «BandParity».«lag_identity'» := P2M_BandParity_lag_identity__1cd92334e44b
