-- Prove2me | Theorems.Thm_P2M_Automata_na_FinRun_of_FinRun__1438a22cbb33
-- name    : P2M_Automata_na_FinRun_of_FinRun__1438a22cbb33
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:21:42.565826+00:00
-- url     : https://prove2.me/theorems/e021fa19-4532-4054-92fb-b584ec7c7276
-- title:
--   P2 M Automata na Fin Run of Fin Run  1438a22cbb33: P2 M Automata na Fin Run of Fin Run  1438a22cbb33
-- statement:
--   The P2 M Automata na Fin Run of Fin Run  1438a22cbb33 construction uses the P2 M Automata na Fin Run of Fin Run  1438a22cbb33 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Basic.lean#L96-L104
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Basic.lean#L96-L104

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Automata_Basic
set_option autoImplicit true
open Function Set Filter Stream'
open Automata
variable {A : Type}
variable {M : NA A} {acc : Set M.State}

theorem P2M_Automata_na_FinRun_of_FinRun__1438a22cbb33 [Inhabited A] {n : ℕ} {as : Fin n → A} {ss : Fin (n + 1) → M.State}
    (h : M.FinRun' n as ss) : M.FinRun n (fun k ↦ if h : k < n then as ⟨k, h⟩ else default)
      (fun k ↦ if h : k < n + 1 then ss ⟨k, h⟩ else ss 0) := by sorry

alias «Automata».«na_FinRun_of_FinRun'» := P2M_Automata_na_FinRun_of_FinRun__1438a22cbb33
