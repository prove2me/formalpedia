-- Prove2me | Theorems.Thm_Sabidussi_OddBalance_choiceTerm_derangement_inv
-- name    : Sabidussi.OddBalance.choiceTerm_derangement_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:09:50.212871+00:00
-- url     : https://prove2.me/theorems/74c46cc7-1d11-5275-aa77-0793baa45ca9
-- title:
--   Odd Balance: choice Term derangement inv
-- statement:
--   The Odd Balance construction uses the choice Term derangement inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/OddBalance.lean#L286-L303
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/OddBalance.lean#L286-L303

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Prod
import Definitions.Def_Sabidussi_OddBalance
set_option autoImplicit true
open scoped BigOperators
open Finset
open Sabidussi
open Sabidussi.OddBalance
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem Sabidussi.OddBalance.choiceTerm_derangement_inv
    (b : V → V → Fin 3 → Fin 3 → F2)
    (hsymm : ∀ v u a c, b v u a c = b u v c a)
    (S : Finset V) (d : Derangement S) (x : V → Fin 3) :
    choiceTerm b S d.inv.choice x = choiceTerm b S d.choice x := by sorry
