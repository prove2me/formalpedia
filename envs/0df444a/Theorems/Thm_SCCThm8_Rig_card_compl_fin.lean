-- Prove2me | Theorems.Thm_SCCThm8_Rig_card_compl_fin
-- name    : SCCThm8.Rig.card_compl_fin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:47:39.043903+00:00
-- url     : https://prove2.me/theorems/0896ccd9-31b2-55b3-8a37-6a713984c5ed
-- title:
--   Rig: card compl fin
-- statement:
--   The Rig construction uses the card compl fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L28-L29
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L28-L29

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Rigidity
set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
open SCCThm8.Rig
variable {n : ℕ}

theorem SCCThm8.Rig.card_compl_fin (s : Finset (Fin n)) : sᶜ.card = n - s.card := by sorry
