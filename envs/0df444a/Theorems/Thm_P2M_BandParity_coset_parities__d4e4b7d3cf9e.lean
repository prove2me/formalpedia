-- Prove2me | Theorems.Thm_P2M_BandParity_coset_parities__d4e4b7d3cf9e
-- name    : P2M_BandParity_coset_parities__d4e4b7d3cf9e
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:08:20.526391+00:00
-- url     : https://prove2.me/theorems/ac3aeb73-5df9-4ad3-86ff-5ca8fd9159a8
-- title:
--   P2 M Band Parity coset parities  d4e4b7d3cf9e: P2 M Band Parity coset parities  d4e4b7d3cf9e
-- statement:
--   **Exact coset parities.** `∑_{u ∈ H} s(u) = k + 2t` and `∑_{u ∈ 2H} s(u) = t - 2k`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L310-L354
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L310-L354

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

theorem P2M_BandParity_coset_parities__d4e4b7d3cf9e (hp8 : p % 8 = 5) (hp5 : 5 < p) (hpin : χ 2 = gi) :
    ∑ u ∈ cls χ 1, parSign u = k χ + 2 * t χ ∧ ∑ u ∈ cls χ gi, parSign u = t χ - 2 * k χ := by sorry

alias «BandParity».«coset_parities'» := P2M_BandParity_coset_parities__d4e4b7d3cf9e
