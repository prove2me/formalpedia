-- Prove2me | Theorems.Thm_Sabidussi_OddBalance_sum_one_fin3_assignments
-- name    : Sabidussi.OddBalance.sum_one_fin3_assignments
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:10:05.684901+00:00
-- url     : https://prove2.me/theorems/bb651695-005c-5eda-9dd0-75ea73009dca
-- title:
--   Odd Balance: sum one fin3 assignments
-- statement:
--   The Odd Balance construction uses the sum one fin3 assignments property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/OddBalance.lean#L489-L493
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/OddBalance.lean#L489-L493

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

theorem Sabidussi.OddBalance.sum_one_fin3_assignments : (∑ _x : V → Fin 3, (1 : F2)) = 1 := by sorry
