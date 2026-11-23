-- Prove2me | Theorems.Thm_P2M_inf_occ_pair__f8f4dbc0c9a2
-- name    : P2M_inf_occ_pair__f8f4dbc0c9a2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:37:43.767203+00:00
-- url     : https://prove2.me/theorems/607dc935-6158-47ab-a78a-dcea28f8dab7
-- title:
--   P2 M inf occ pair  f8f4dbc0c9a2: P2 M inf occ pair  f8f4dbc0c9a2
-- statement:
--   The P2 M inf occ pair  f8f4dbc0c9a2 construction uses the P2 M inf occ pair  f8f4dbc0c9a2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/InfOcc.lean#L142-L165
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/InfOcc.lean#L142-L165

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_InfOcc
set_option autoImplicit true
open Function Set Prod Option Filter Stream'
open Classical
attribute [local instance_reducible] Stream'

theorem P2M_inf_occ_pair__f8f4dbc0c9a2 {X1 : Type u} {X2 : Type v} [Finite X1] [Finite X2] (xs : Stream' (X1 × X2)) :
    fst '' (InfOcc xs) = InfOcc (fst ∘ xs) ∧
    snd '' (InfOcc xs) = InfOcc (snd ∘ xs) := by sorry

alias «inf_occ_pair'» := P2M_inf_occ_pair__f8f4dbc0c9a2
