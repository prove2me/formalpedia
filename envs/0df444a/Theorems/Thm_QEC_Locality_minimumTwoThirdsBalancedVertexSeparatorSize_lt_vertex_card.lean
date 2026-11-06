-- Prove2me | Theorems.Thm_QEC_Locality_minimumTwoThirdsBalancedVertexSeparatorSize_lt_vertex_card
-- name    : QEC.Locality.minimumTwoThirdsBalancedVertexSeparatorSize_lt_vertex_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:30:52.812+00:00
-- url     : https://prove2.me/theorems/587fa695-5947-4571-a137-e7a65ad0cd1d
-- title:
--   Locality: minimum Two Thirds Balanced Vertex Separator Size lt vertex card
-- statement:
--   With at least two vertices, deleting all but one is a proper balanced separator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/MaxFamily.lean#L125-L141
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/MaxFamily.lean#L125-L141

import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u v

theorem QEC.Locality.minimumTwoThirdsBalancedVertexSeparatorSize_lt_vertex_card
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (vertices : Finset ι)
    (hcard : 2 ≤ vertices.card) :
    minimumTwoThirdsBalancedVertexSeparatorSize G vertices < vertices.card := by sorry
