-- Prove2me | Theorems.Thm_QEC_Locality_inducedSubgraph_adj_iff
-- name    : QEC.Locality.inducedSubgraph_adj_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:37:49.705202+00:00
-- url     : https://prove2.me/theorems/6325b559-9be2-490d-a904-9fe212bcb12b
-- title:
--   Locality: induced Subgraph adj iff
-- statement:
--   Induced adjacency is exactly the original graph relation restricted to listed vertices.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/Core.lean#L34-L38
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/Core.lean#L34-L38

import Mathlib
import Definitions.Def_QEC_Locality_Graph_Core
set_option autoImplicit false
open QEC QEC.Locality
universe u

theorem QEC.Locality.inducedSubgraph_adj_iff {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (vertices : Finset ι)
    (x y : {i : ι // i ∈ vertices}) :
    (inducedSubgraph G vertices).adjacent x y ↔ G.adjacent x.1 y.1 := by sorry
