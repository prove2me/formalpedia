-- Prove2me | Theorems.Thm_P2M_Automata_na_AcceptedLang_of_FinAccept__52bfd9b970d5
-- name    : P2M_Automata_na_AcceptedLang_of_FinAccept__52bfd9b970d5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:32:28.127797+00:00
-- url     : https://prove2.me/theorems/49852312-e139-478a-b1a5-c1ee55ad3f39
-- title:
--   P2 M Automata na Accepted Lang of Fin Accept  52bfd9b970d5: P2 M Automata na Accepted Lang of Fin Accept  52bfd9b970d5
-- statement:
--   The following theorem shows that under the assumption that the alphabet type `A`
--   is inhabited, the definitions using infinite sequences and those using finite sequences
--   actually define the same notion of the accepted language of an automaton.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Basic.lean#L126-L140
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Basic.lean#L126-L140

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Automata_Basic
set_option autoImplicit true
open Function Set Filter Stream'
open Automata
variable {A : Type}
variable {M : NA A} {acc : Set M.State}

theorem P2M_Automata_na_AcceptedLang_of_FinAccept__52bfd9b970d5 [Inhabited A] :
    M.AcceptedLang acc = { al | ∃ n as, M.FinAccept' acc n as ∧ List.ofFn as = al } := by sorry

alias «Automata».«na_AcceptedLang_of_FinAccept'» := P2M_Automata_na_AcceptedLang_of_FinAccept__52bfd9b970d5
