-- Prove2me | Theorems.Thm_QEC_Locality_minimumTwoThirdsBalancedVertexSeparatorSize_mono_spanningSubgraph
-- name    : QEC.Locality.minimumTwoThirdsBalancedVertexSeparatorSize_mono_spanningSubgraph
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:34:53.276354+00:00
-- url     : https://prove2.me/theorems/d724d3f0-956b-4c9a-b745-b8f9ab84208e
-- title:
--   Locality: minimum Two Thirds Balanced Vertex Separator Size mono spanning Subgraph
-- statement:
--   Deleting edges cannot increase the minimum separator of a fixed vertex set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/EdgeDivision.lean#L49-L58
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/EdgeDivision.lean#L49-L58

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
set_option autoImplicit false
open QEC QEC.Locality
open QEC Semantics Coding
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.minimumTwoThirdsBalancedVertexSeparatorSize_mono_spanningSubgraph
    {H G : ConnectivityGraph ι} (hHG : IsSpanningSubgraph H G)
    (vertices : Finset ι) :
    minimumTwoThirdsBalancedVertexSeparatorSize H vertices ≤
      minimumTwoThirdsBalancedVertexSeparatorSize G vertices := by sorry
