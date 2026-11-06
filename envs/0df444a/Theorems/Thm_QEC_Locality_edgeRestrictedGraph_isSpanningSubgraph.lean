-- Prove2me | Theorems.Thm_QEC_Locality_edgeRestrictedGraph_isSpanningSubgraph
-- name    : QEC.Locality.edgeRestrictedGraph_isSpanningSubgraph
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:42:15.570025+00:00
-- url     : https://prove2.me/theorems/d6af8127-a55d-4e2f-aa95-a4546ac2122b
-- title:
--   Locality: edge Restricted Graph is Spanning Subgraph
-- statement:
--   Finite edge restriction is a spanning subgraph.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Recursion.lean#L63-L67
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Recursion.lean#L63-L67

import Definitions.Def_QEC_Locality_SeparatorProfile_EdgeDivision
import Definitions.Def_QEC_Locality_SeparatorProfile_Recursion
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem QEC.Locality.edgeRestrictedGraph_isSpanningSubgraph
    (G : ConnectivityGraph ι) (edges : Finset (ι × ι)) :
    IsSpanningSubgraph (edgeRestrictedGraph G edges) G := by sorry
