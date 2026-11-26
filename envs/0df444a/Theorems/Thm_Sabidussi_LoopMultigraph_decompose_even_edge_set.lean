-- Prove2me | Theorems.Thm_Sabidussi_LoopMultigraph_decompose_even_edge_set
-- name    : Sabidussi.LoopMultigraph.decompose_even_edge_set
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:10:14.439902+00:00
-- url     : https://prove2.me/theorems/96d27d93-a3d9-4126-a8a6-311589113425
-- title:
--   Loop Multigraph: decompose even edge set
-- statement:
--   Every finite even edge set is an edge-disjoint union of multigraph cycles.  The displayed
--   equation records edge multiplicities and is stronger than mere equality of unions.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/LoopMultigraph.lean#L194-L233
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/LoopMultigraph.lean#L194-L233

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
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LoopMultigraph V E)

theorem Sabidussi.LoopMultigraph.decompose_even_edge_set (F : Finset E) (hF : G.IsEvenEdgeSet F) :
    ∃ L : List G.Cycle,
      ∀ e : E, (L.filter fun C ↦ e ∈ C.edges).length = if e ∈ F then 1 else 0 := by sorry
