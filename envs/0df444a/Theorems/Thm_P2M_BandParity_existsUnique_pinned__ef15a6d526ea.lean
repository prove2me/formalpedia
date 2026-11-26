-- Prove2me | Theorems.Thm_P2M_BandParity_existsUnique_pinned__ef15a6d526ea
-- name    : P2M_BandParity_existsUnique_pinned__ef15a6d526ea
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:55:30.021908+00:00
-- url     : https://prove2.me/theorems/9c9f3861-9cfa-4c09-9795-af7598312f46
-- title:
--   P2 M Band Parity exists Unique pinned  ef15a6d526ea: P2 M Band Parity exists Unique pinned  ef15a6d526ea
-- statement:
--   **Definition 3.3 (the pin).** For `p ≡ 5 (mod 8)` there is a unique quartic character
--   modulo `p` with `χ 2 = i`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Pin.lean#L49-L78
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Pin.lean#L49-L78

module
public import Definitions.Def_BandParity_Basic
public import Definitions.Def_BandParity_Pin
set_option autoImplicit true
@[expose] public section
public section
open BandParity
variable {p : ℕ} [hp : Fact p.Prime]

theorem P2M_BandParity_existsUnique_pinned__ef15a6d526ea (hp8 : p % 8 = 5) :
    ∃! χ : MulChar (ZMod p) GaussianInt, orderOf χ = 4 ∧ χ 2 = gi := by sorry

alias «BandParity».«existsUnique_pinned'» := P2M_BandParity_existsUnique_pinned__ef15a6d526ea
