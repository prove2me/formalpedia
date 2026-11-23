-- Prove2me | Theorems.Thm_P2M_Automata_na_FinAccept_of_FinAccept__3d26c8363d5d
-- name    : P2M_Automata_na_FinAccept_of_FinAccept__3d26c8363d5d
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:21:41.880453+00:00
-- url     : https://prove2.me/theorems/95f48b44-33e7-46a7-9bde-66bba5085e2c
-- title:
--   P2 M Automata na Fin Accept of Fin Accept  3d26c8363d5d: P2 M Automata na Fin Accept of Fin Accept  3d26c8363d5d
-- statement:
--   The P2 M Automata na Fin Accept of Fin Accept  3d26c8363d5d construction uses the P2 M Automata na Fin Accept of Fin Accept  3d26c8363d5d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Basic.lean#L114-L120
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Basic.lean#L114-L120

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Automata_Basic
set_option autoImplicit true
open Function Set Filter Stream'
open Automata
variable {A : Type}
variable {M : NA A} {acc : Set M.State}

theorem P2M_Automata_na_FinAccept_of_FinAccept__3d26c8363d5d [Inhabited A] {n : ℕ} {as : Fin n → A}
    (h : M.FinAccept' acc n as) : M.FinAccept acc n (fun k ↦ if h : k < n then as ⟨k, h⟩ else default) := by sorry

alias «Automata».«na_FinAccept_of_FinAccept'» := P2M_Automata_na_FinAccept_of_FinAccept__3d26c8363d5d
