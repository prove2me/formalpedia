-- Prove2me | Theorems.Thm_QEC_Locality_WeightedBoundaryEdgeRecursion_initialBoundary_incident_subset_ownerBoundary
-- name    : QEC.Locality.WeightedBoundaryEdgeRecursion.initialBoundary_incident_subset_ownerBoundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:42:16.397916+00:00
-- url     : https://prove2.me/theorems/216f2e1a-e1ed-4d0e-b436-70cd9f903938
-- title:
--   Weighted Boundary Edge Recursion: initial Boundary incident subset owner Boundary
-- statement:
--   An inherited boundary vertex that remains incident is retained to the leaf.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/WeightedRefinement.lean#L817-L868
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/WeightedRefinement.lean#L817-L868

import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedRecursion
import Definitions.Def_QEC_Locality_SeparatorProfile_Weighted
import Definitions.Def_QEC_Locality_SeparatorProfile_WeightedRefinement
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.WeightedBoundaryEdgeRecursion.initialBoundary_incident_subset_ownerBoundary
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary)
    (owner : tree.edgeOwnerType) :
    boundary ∩ edgeIncidentVertices (tree.edgeRegion owner) ⊆ tree.ownerBoundary owner := by sorry
