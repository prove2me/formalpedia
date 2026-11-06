-- Prove2me | Theorems.Thm_QEC_Locality_separatorRightEdges_incident_subset
-- name    : QEC.Locality.separatorRightEdges_incident_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:12:44.904624+00:00
-- url     : https://prove2.me/theorems/c468ce8e-36f4-4416-a9c7-19753f2c355c
-- title:
--   Locality: separator Right Edges incident subset
-- statement:
--   The right child carrier contains every endpoint of its allocated edge set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/StoppedRecursion.lean#L100-L145
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/StoppedRecursion.lean#L100-L145

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedRecursion
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.separatorRightEdges_incident_subset
    (G : ConnectivityGraph ι) (edges : Finset (ι × ι))
    (vertices left separator right : Finset ι)
    (hsubset : edges ⊆ directedEdgeFinset G)
    (hsymmetric : ReverseSymmetricEdgeSet edges)
    (hincident : edgeIncidentVertices edges ⊆ vertices)
    (hpartition :
      TwoThirdsBalancedPartitionAfterDeleting (edgeRestrictedGraph G edges)
        vertices left separator right) :
    edgeIncidentVertices (separatorRightEdges edges left) ⊆ right ∪ separator := by sorry
