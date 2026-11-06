-- Prove2me | Theorems.Thm_QEC_Locality_IsTwoThirdsBalancedVertexSeparator_mono_spanningSubgraph
-- name    : QEC.Locality.IsTwoThirdsBalancedVertexSeparator.mono_spanningSubgraph
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:35:25.413713+00:00
-- url     : https://prove2.me/theorems/8264a77a-1945-472b-9124-e3f32f01981e
-- title:
--   Is Two Thirds Balanced Vertex Separator: mono spanning Subgraph
-- statement:
--   Every balanced separator for a graph remains balanced after deleting edges.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/EdgeDivision.lean#L38-L46
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/EdgeDivision.lean#L38-L46

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
set_option autoImplicit false
open QEC QEC.Locality
open QEC Semantics Coding
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.IsTwoThirdsBalancedVertexSeparator.mono_spanningSubgraph
    {H G : ConnectivityGraph ι} (hHG : IsSpanningSubgraph H G)
    {vertices separator : Finset ι}
    (hseparator : IsTwoThirdsBalancedVertexSeparator G vertices separator) :
    IsTwoThirdsBalancedVertexSeparator H vertices separator := by sorry
