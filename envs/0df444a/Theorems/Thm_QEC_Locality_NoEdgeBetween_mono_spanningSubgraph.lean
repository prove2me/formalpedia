-- Prove2me | Theorems.Thm_QEC_Locality_NoEdgeBetween_mono_spanningSubgraph
-- name    : QEC.Locality.NoEdgeBetween.mono_spanningSubgraph
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:14:38.302257+00:00
-- url     : https://prove2.me/theorems/9665cb3d-f9c1-4100-9f8f-a1c421ce356c
-- title:
--   No Edge Between: mono spanning Subgraph
-- statement:
--   A no-cross-edge certificate survives deletion of graph edges.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/EdgeDivision.lean#L30-L35
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/EdgeDivision.lean#L30-L35

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
set_option autoImplicit false
open QEC QEC.Locality
open QEC Semantics Coding
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.NoEdgeBetween.mono_spanningSubgraph
    {H G : ConnectivityGraph ι} (hHG : IsSpanningSubgraph H G)
    {left right : Finset ι} (hnoEdge : NoEdgeBetween G left right) :
    NoEdgeBetween H left right := by sorry
