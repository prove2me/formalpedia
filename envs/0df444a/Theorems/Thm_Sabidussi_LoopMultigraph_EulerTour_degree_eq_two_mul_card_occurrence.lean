-- Prove2me | Theorems.Thm_Sabidussi_LoopMultigraph_EulerTour_degree_eq_two_mul_card_occurrence
-- name    : Sabidussi.LoopMultigraph.EulerTour.degree_eq_two_mul_card_occurrence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:11:13.774068+00:00
-- url     : https://prove2.me/theorems/0fcdc522-f726-5fd9-bb3a-b40971926e81
-- title:
--   Euler Tour: degree eq two mul card occurrence
-- statement:
--   The degree at `v` is twice its number of occurrences in the transition word.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/LoopMultigraph.lean#L137-L140
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/LoopMultigraph.lean#L137-L140

import Definitions.Def_Sabidussi_Color
import Definitions.Def_Sabidussi_Statement
import Mathlib.Data.Fin.Rev
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finite.Set
import Mathlib.Data.Fintype.Sets
import Definitions.Def_Sabidussi_LoopMultigraph
set_option autoImplicit true
open Sabidussi
open scoped BigOperators
open Sabidussi.LoopMultigraph
variable {V E : Type*} [Fintype V] [Fintype E]
open Sabidussi.LoopMultigraph.EulerTour
variable [DecidableEq V] {G : LoopMultigraph V E} (T : G.EulerTour)

theorem Sabidussi.LoopMultigraph.EulerTour.degree_eq_two_mul_card_occurrence (v : V) :
    G.degree v = 2 * Fintype.card (T.Occurrence v) := by sorry
