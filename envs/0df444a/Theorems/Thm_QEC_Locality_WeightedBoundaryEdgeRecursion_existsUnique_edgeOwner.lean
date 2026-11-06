-- Prove2me | Theorems.Thm_QEC_Locality_WeightedBoundaryEdgeRecursion_existsUnique_edgeOwner
-- name    : QEC.Locality.WeightedBoundaryEdgeRecursion.existsUnique_edgeOwner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:41:52.986521+00:00
-- url     : https://prove2.me/theorems/1716ca2b-21ea-4353-84b9-983a7613aa6f
-- title:
--   Weighted Boundary Edge Recursion: exists Unique edge Owner
-- statement:
--   The Weighted Boundary Edge Recursion construction uses the exists Unique edge Owner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/WeightedRefinement.lean#L569-L656
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/WeightedRefinement.lean#L569-L656

import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedRecursion
import Definitions.Def_QEC_Locality_SeparatorProfile_Weighted
import Definitions.Def_QEC_Locality_SeparatorProfile_WeightedRefinement
import Theorems.Thm_QEC_Locality_EdgeRestrictedStoppedRecursion_existsUnique_edgeOwner

set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.WeightedBoundaryEdgeRecursion.existsUnique_edgeOwner
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary)
    (edge : ι × ι) (hedge : edge ∈ edges) :
    ∃! owner : tree.edgeOwnerType, edge ∈ tree.edgeRegion owner := by sorry
