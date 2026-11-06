-- Prove2me | Theorems.Thm_QEC_Locality_edgeDivision_edges_cover
-- name    : QEC.Locality.edgeDivision_edges_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:22:02.07494+00:00
-- url     : https://prove2.me/theorems/c05f2c27-8b03-4a18-8c28-2908a35322c9
-- title:
--   Locality: edge Division edges cover
-- statement:
--   The active region edge sets cover exactly the graph edges.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/EdgeDivision.lean#L112-L124
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/EdgeDivision.lean#L112-L124

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
set_option autoImplicit false
open QEC QEC.Locality
open QEC Semantics Coding
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.edgeDivision_edges_cover {m : Type w} [DecidableEq m]
    {G : ConnectivityGraph ι} {regions : m → Finset (ι × ι)}
    {active : Finset m} (hDivision : IsEdgeDivision G regions active) :
    active.biUnion regions = directedEdgeFinset G := by sorry
