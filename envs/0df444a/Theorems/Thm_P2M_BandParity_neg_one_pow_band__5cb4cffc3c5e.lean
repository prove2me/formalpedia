-- Prove2me | Theorems.Thm_P2M_BandParity_neg_one_pow_band__5cb4cffc3c5e
-- name    : P2M_BandParity_neg_one_pow_band__5cb4cffc3c5e
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:01:17.821348+00:00
-- url     : https://prove2.me/theorems/08616f2f-8a7f-5867-ad79-e2577d279af6
-- title:
--   P2 M Band Parity neg one pow band  5cb4cffc3c5e: P2 M Band Parity neg one pow band  5cb4cffc3c5e
-- statement:
--   **Parity dictionary.** `(-1)^{⌊⟨x⟩²/p⌋} = s(x) s(x²)`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L68-L85
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L68-L85

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

theorem P2M_BandParity_neg_one_pow_band__5cb4cffc3c5e (hp2 : p ≠ 2) (x : ZMod p) :
    (-1 : ℤ) ^ band x = parSign x * parSign (x ^ 2) := by sorry

alias «BandParity».«neg_one_pow_band'» := P2M_BandParity_neg_one_pow_band__5cb4cffc3c5e
