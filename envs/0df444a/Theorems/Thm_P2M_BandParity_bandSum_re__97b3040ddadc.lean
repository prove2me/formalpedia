-- Prove2me | Theorems.Thm_P2M_BandParity_bandSum_re__97b3040ddadc
-- name    : P2M_BandParity_bandSum_re__97b3040ddadc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:03:45.20026+00:00
-- url     : https://prove2.me/theorems/19de8cbd-a248-583d-b295-387ef1e69cf6
-- title:
--   P2 M Band Parity band Sum re  97b3040ddadc: P2 M Band Parity band Sum re  97b3040ddadc
-- statement:
--   `f = ∑_{u ∈ H} s(u) s(u²)`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L265-L267
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L265-L267

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

theorem P2M_BandParity_bandSum_re__97b3040ddadc (hp8 : p % 8 = 5) :
    (bandSum χ).re = ∑ u ∈ cls χ 1, parSign u * parSign (u ^ 2) := by sorry

alias «BandParity».«bandSum_re'» := P2M_BandParity_bandSum_re__97b3040ddadc
