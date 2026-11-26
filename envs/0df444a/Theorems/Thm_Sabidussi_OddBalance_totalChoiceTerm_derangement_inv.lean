-- Prove2me | Theorems.Thm_Sabidussi_OddBalance_totalChoiceTerm_derangement_inv
-- name    : Sabidussi.OddBalance.totalChoiceTerm_derangement_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:09:48.72868+00:00
-- url     : https://prove2.me/theorems/ea83de9a-a2cb-5ea4-ad87-ad387d1775ad
-- title:
--   Odd Balance: total Choice Term derangement inv
-- statement:
--   The Odd Balance construction uses the total Choice Term derangement inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/OddBalance.lean#L305-L312
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/OddBalance.lean#L305-L312

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

theorem Sabidussi.OddBalance.totalChoiceTerm_derangement_inv
    (b : V → V → Fin 3 → Fin 3 → F2)
    (hsymm : ∀ v u a c, b v u a c = b u v c a)
    (S : Finset V) (d : Derangement S) :
    totalChoiceTerm b S d.inv.choice = totalChoiceTerm b S d.choice := by sorry
