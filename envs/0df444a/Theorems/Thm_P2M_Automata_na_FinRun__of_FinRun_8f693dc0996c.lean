-- Prove2me | Theorems.Thm_P2M_Automata_na_FinRun__of_FinRun_8f693dc0996c
-- name    : P2M_Automata_na_FinRun__of_FinRun_8f693dc0996c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:21:44.429352+00:00
-- url     : https://prove2.me/theorems/befb64ce-4939-4e6a-88e6-45ba992bc261
-- title:
--   P2 M Automata na Fin Run  of Fin Run 8f693dc0996c: P2 M Automata na Fin Run  of Fin Run 8f693dc0996c
-- statement:
--   The P2 M Automata na Fin Run  of Fin Run 8f693dc0996c construction uses the P2 M Automata na Fin Run  of Fin Run 8f693dc0996c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Basic.lean#L88-L94
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Basic.lean#L88-L94

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Automata_Basic
set_option autoImplicit true
open Function Set Filter Stream'
open Automata
variable {A : Type}
variable {M : NA A} {acc : Set M.State}

theorem P2M_Automata_na_FinRun__of_FinRun_8f693dc0996c {n : ℕ} {as : Stream' A} {ss : Stream' M.State}
    (h : M.FinRun n as ss) : M.FinRun' n (fun k ↦ as k) (fun k ↦ ss k) := by sorry

alias «Automata».«na_FinRun'_of_FinRun» := P2M_Automata_na_FinRun__of_FinRun_8f693dc0996c
