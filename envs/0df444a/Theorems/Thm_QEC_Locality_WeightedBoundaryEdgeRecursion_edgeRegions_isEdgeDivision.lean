-- Prove2me | Theorems.Thm_QEC_Locality_WeightedBoundaryEdgeRecursion_edgeRegions_isEdgeDivision
-- name    : QEC.Locality.WeightedBoundaryEdgeRecursion.edgeRegions_isEdgeDivision
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:43:47.969884+00:00
-- url     : https://prove2.me/theorems/fd2ce2a8-aa59-4041-b476-f0c86acd3ff4
-- title:
--   Weighted Boundary Edge Recursion: edge Regions is Edge Division
-- statement:
--   The Weighted Boundary Edge Recursion construction uses the edge Regions is Edge Division property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/WeightedRefinement.lean#L658-L677
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/WeightedRefinement.lean#L658-L677

import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedRecursion
import Definitions.Def_QEC_Locality_SeparatorProfile_Weighted
import Definitions.Def_QEC_Locality_SeparatorProfile_WeightedRefinement
import Theorems.Thm_QEC_Locality_EdgeRestrictedStoppedRecursion_edgeRegions_isEdgeDivision

set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.WeightedBoundaryEdgeRecursion.edgeRegions_isEdgeDivision
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary)
    (hroot : edges = directedEdgeFinset G) :
    IsEdgeDivision G tree.edgeRegion tree.edgeActive := by sorry
