-- Prove2me | Theorems.Thm_Sabidussi_OddBalance_Derangement_inv_inv
-- name    : Sabidussi.OddBalance.Derangement.inv_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:09:47.548733+00:00
-- url     : https://prove2.me/theorems/0e01c8fb-0f8f-512f-8805-0b9ea2267d46
-- title:
--   Derangement: inv inv
-- statement:
--   The Derangement construction uses the inv inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/OddBalance.lean#L282-L284
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/OddBalance.lean#L282-L284

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

theorem Sabidussi.OddBalance.Derangement.inv_inv {S : Finset V} (d : Derangement S) : d.inv.inv = d := by sorry
