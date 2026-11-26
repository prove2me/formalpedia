-- Prove2me | Theorems.Thm_Sabidussi_LoopMultigraph_decompose_even_edge_set_ordinary
-- name    : Sabidussi.LoopMultigraph.decompose_even_edge_set_ordinary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:15:38.941326+00:00
-- url     : https://prove2.me/theorems/fb851067-613e-4df0-92e9-974364a6f966
-- title:
--   Loop Multigraph: decompose even edge set ordinary
-- statement:
--   The existing minimal-even-set decomposition can therefore be read as a decomposition into
--   ordinary connected 2-regular circuits.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/OrdinaryCircuit.lean#L394-L400
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/OrdinaryCircuit.lean#L394-L400

import Definitions.Def_Sabidussi_LoopGraphBridge
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_Sabidussi_OrdinaryCircuit
set_option autoImplicit true
open Sabidussi
open Sabidussi.LoopMultigraph
open scoped BigOperators
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LoopMultigraph V E)

theorem Sabidussi.LoopMultigraph.decompose_even_edge_set_ordinary (F : Finset E) (hF : G.IsEvenEdgeSet F) :
    ∃ L : List G.OrdinaryCircuit,
      ∀ e : E, (L.filter fun C ↦ e ∈ C.edges).length = if e ∈ F then 1 else 0 := by sorry
