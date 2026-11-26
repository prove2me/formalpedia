-- Prove2me | Theorems.Thm_P2M_BandParity_odd_k__12c0ba03e16b
-- name    : P2M_BandParity_odd_k__12c0ba03e16b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:55:53.606617+00:00
-- url     : https://prove2.me/theorems/f6d7a0bf-f832-4779-896d-4929c38f7701
-- title:
--   P2 M Band Parity odd k  12c0ba03e16b: P2 M Band Parity odd k  12c0ba03e16b
-- statement:
--   **Proposition 3.2 (oddness of `k`).**
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/CosetSums.lean#L199-L205
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/CosetSums.lean#L199-L205

module
public import Definitions.Def_BandParity_Pin
public import Definitions.Def_BandParity_FixedBase
public import Definitions.Def_BandParity_CosetSums
set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ

theorem P2M_BandParity_odd_k__12c0ba03e16b (hp8 : p % 8 = 5) (hp5 : 5 < p) : Odd (k χ) := by sorry

alias «BandParity».«odd_k'» := P2M_BandParity_odd_k__12c0ba03e16b
