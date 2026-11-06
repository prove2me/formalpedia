-- Prove2me | Theorems.Thm_QEC_Locality_vertexRestrictedGraph_isSpanningSubgraph
-- name    : QEC.Locality.vertexRestrictedGraph_isSpanningSubgraph
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:37:58.061521+00:00
-- url     : https://prove2.me/theorems/7c2dcbcc-5354-48ba-b8c9-fc850eb150a5
-- title:
--   Locality: vertex Restricted Graph is Spanning Subgraph
-- statement:
--   Vertex restriction is an edge deletion on the same ambient type.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Recursion.lean#L36-L40
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Recursion.lean#L36-L40

import Definitions.Def_QEC_Locality_SeparatorProfile_EdgeDivision
import Definitions.Def_QEC_Locality_SeparatorProfile_Recursion
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem QEC.Locality.vertexRestrictedGraph_isSpanningSubgraph
    (G : ConnectivityGraph ι) (vertices : Finset ι) :
    IsSpanningSubgraph (vertexRestrictedGraph G vertices) G := by sorry
