-- Prove2me | Theorems.Thm_QEC_Locality_WeightedBoundaryEdgeRecursion_localSharedBoundary_subset_ownerBoundary
-- name    : QEC.Locality.WeightedBoundaryEdgeRecursion.localSharedBoundary_subset_ownerBoundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:42:38.807353+00:00
-- url     : https://prove2.me/theorems/17159f6c-3092-4499-9205-487853cd7c3b
-- title:
--   Weighted Boundary Edge Recursion: local Shared Boundary subset owner Boundary
-- statement:
--   Every shared vertex incident to a terminal region is charged to its leaf boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/WeightedRefinement.lean#L871-L1098
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/WeightedRefinement.lean#L871-L1098

import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedRecursion
import Definitions.Def_QEC_Locality_SeparatorProfile_Weighted
import Definitions.Def_QEC_Locality_SeparatorProfile_WeightedRefinement
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.WeightedBoundaryEdgeRecursion.localSharedBoundary_subset_ownerBoundary
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary)
    (owner : tree.edgeOwnerType) :
    edgeIncidentVertices (tree.edgeRegion owner) ∩
        edgeDivisionSharedBoundary tree.edgeRegion tree.edgeActive ⊆
      tree.ownerBoundary owner := by sorry
