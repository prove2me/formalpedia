-- Prove2me | Theorems.Thm_Sabidussi_LoopMultigraph_EulerTour_arrival_eq_vertexAt_next
-- name    : Sabidussi.LoopMultigraph.EulerTour.arrival_eq_vertexAt_next
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:14:41.189257+00:00
-- url     : https://prove2.me/theorems/26295a9d-e178-4d48-88af-f2b0faaa9a78
-- title:
--   Euler Tour: arrival eq vertex At next
-- statement:
--   The Euler Tour construction uses the arrival eq vertex At next property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/LoopMultigraph.lean#L43-L44
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/LoopMultigraph.lean#L43-L44

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

theorem Sabidussi.LoopMultigraph.EulerTour.arrival_eq_vertexAt_next (i : T.Pos) : T.arrivalAt i = T.vertexAt (T.next i) := by sorry
