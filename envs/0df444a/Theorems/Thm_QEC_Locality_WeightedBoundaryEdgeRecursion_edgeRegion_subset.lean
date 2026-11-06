-- Prove2me | Theorems.Thm_QEC_Locality_WeightedBoundaryEdgeRecursion_edgeRegion_subset
-- name    : QEC.Locality.WeightedBoundaryEdgeRecursion.edgeRegion_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:42:37.545423+00:00
-- url     : https://prove2.me/theorems/d89c145e-0df9-4d4c-892d-356fd55698a1
-- title:
--   Weighted Boundary Edge Recursion: edge Region subset
-- statement:
--   The Weighted Boundary Edge Recursion construction uses the edge Region subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/WeightedRefinement.lean#L504-L518
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/WeightedRefinement.lean#L504-L518

import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedRecursion
import Definitions.Def_QEC_Locality_SeparatorProfile_Weighted
import Definitions.Def_QEC_Locality_SeparatorProfile_WeightedRefinement
import Theorems.Thm_QEC_Locality_EdgeRestrictedStoppedRecursion_edgeRegion_subset

set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.WeightedBoundaryEdgeRecursion.edgeRegion_subset
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary)
    (owner : tree.edgeOwnerType) : tree.edgeRegion owner ⊆ edges := by sorry
