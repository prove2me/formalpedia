-- Prove2me | Theorems.Thm_P2M_Automata_na_FinAccept__of_FinAccept_fdb8c514268d
-- name    : P2M_Automata_na_FinAccept__of_FinAccept_fdb8c514268d
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:21:39.709676+00:00
-- url     : https://prove2.me/theorems/9cef3590-da0e-4aee-8b17-ef8d73015eb6
-- title:
--   P2 M Automata na Fin Accept  of Fin Accept fdb8c514268d: P2 M Automata na Fin Accept  of Fin Accept fdb8c514268d
-- statement:
--   The P2 M Automata na Fin Accept  of Fin Accept fdb8c514268d construction uses the P2 M Automata na Fin Accept  of Fin Accept fdb8c514268d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Basic.lean#L106-L112
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Basic.lean#L106-L112

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Automata_Basic
set_option autoImplicit true
open Function Set Filter Stream'
open Automata
variable {A : Type}
variable {M : NA A} {acc : Set M.State}

theorem P2M_Automata_na_FinAccept__of_FinAccept_fdb8c514268d {n : ℕ} {as : Stream' A}
    (h : M.FinAccept acc n as) : M.FinAccept' acc n (fun k ↦ as k) := by sorry

alias «Automata».«na_FinAccept'_of_FinAccept» := P2M_Automata_na_FinAccept__of_FinAccept_fdb8c514268d
