-- Prove2me | Theorems.Thm_P2M_BandParity_bandSum_im__7ed5aaa03d73
-- name    : P2M_BandParity_bandSum_im__7ed5aaa03d73
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:04:35.823432+00:00
-- url     : https://prove2.me/theorems/15e64602-6d73-4d3f-b988-6798d49ed888
-- title:
--   P2 M Band Parity band Sum im  7ed5aaa03d73: P2 M Band Parity band Sum im  7ed5aaa03d73
-- statement:
--   `e = ∑_{u ∈ 2H} s(u) s(u²)`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L270-L272
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L270-L272

module
public import Definitions.Def_BandParity_Defs
public import Definitions.Def_BandParity_Matching
public import Definitions.Def_BandParity_Laws
set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ

theorem P2M_BandParity_bandSum_im__7ed5aaa03d73 (hp8 : p % 8 = 5) :
    (bandSum χ).im = ∑ u ∈ cls χ gi, parSign u * parSign (u ^ 2) := by sorry

alias «BandParity».«bandSum_im'» := P2M_BandParity_bandSum_im__7ed5aaa03d73
