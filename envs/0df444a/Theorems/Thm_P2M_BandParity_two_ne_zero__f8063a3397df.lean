-- Prove2me | Theorems.Thm_P2M_BandParity_two_ne_zero__f8063a3397df
-- name    : P2M_BandParity_two_ne_zero__f8063a3397df
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:02:43.064299+00:00
-- url     : https://prove2.me/theorems/64883802-a2e5-4b9c-8e2e-9d2579f34a87
-- title:
--   P2 M Band Parity two ne zero  f8063a3397df: P2 M Band Parity two ne zero  f8063a3397df
-- statement:
--   The P2 M Band Parity two ne zero  f8063a3397df construction uses the P2 M Band Parity two ne zero  f8063a3397df property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L56-L57
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L56-L57

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

theorem P2M_BandParity_two_ne_zero__f8063a3397df (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by sorry

alias «BandParity».«two_ne_zero'» := P2M_BandParity_two_ne_zero__f8063a3397df
