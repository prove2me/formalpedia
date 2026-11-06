-- Prove2me | Theorems.Thm_QEC_Locality_separatorLeftEdges_incident_subset
-- name    : QEC.Locality.separatorLeftEdges_incident_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:12:19.096821+00:00
-- url     : https://prove2.me/theorems/d79c5d48-97b0-461e-ae2c-8215449b3f7a
-- title:
--   Locality: separator Left Edges incident subset
-- statement:
--   The left child carrier contains every endpoint of its allocated edge set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/StoppedRecursion.lean#L47-L97
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/StoppedRecursion.lean#L47-L97

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedRecursion
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.separatorLeftEdges_incident_subset
    (G : ConnectivityGraph ι) (edges : Finset (ι × ι))
    (vertices left separator right : Finset ι)
    (hsubset : edges ⊆ directedEdgeFinset G)
    (hsymmetric : ReverseSymmetricEdgeSet edges)
    (hincident : edgeIncidentVertices edges ⊆ vertices)
    (hpartition :
      TwoThirdsBalancedPartitionAfterDeleting (edgeRestrictedGraph G edges)
        vertices left separator right) :
    edgeIncidentVertices (separatorLeftEdges edges left) ⊆ left ∪ separator := by sorry
