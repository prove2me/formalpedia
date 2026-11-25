-- Prove2me | Theorems.Thm_SCCThm8_Rig_card_sw
-- name    : SCCThm8.Rig.card_sw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:47:23.054988+00:00
-- url     : https://prove2.me/theorems/8a4becc4-42f8-5e02-8b6f-8975c1b7b345
-- title:
--   Rig: card sw
-- statement:
--   The Rig construction uses the card sw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L21-L26
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L21-L26

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

theorem SCCThm8.Rig.card_sw {A : Finset (Fin n)} {k : ℕ} {i j : Fin n} (hA : A.card = k) (hi : i ∈ A)
    (hj : j ∉ A) : (sw A i j).card = k := by sorry
