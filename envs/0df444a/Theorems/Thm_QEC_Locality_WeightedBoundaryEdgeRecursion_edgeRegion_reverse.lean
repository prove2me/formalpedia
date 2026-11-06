-- Prove2me | Theorems.Thm_QEC_Locality_WeightedBoundaryEdgeRecursion_edgeRegion_reverse
-- name    : QEC.Locality.WeightedBoundaryEdgeRecursion.edgeRegion_reverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:42:13.878374+00:00
-- url     : https://prove2.me/theorems/9f8de771-844d-4877-98ad-d9e412b7903d
-- title:
--   Weighted Boundary Edge Recursion: edge Region reverse
-- statement:
--   The Weighted Boundary Edge Recursion construction uses the edge Region reverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/WeightedRefinement.lean#L520-L534
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/WeightedRefinement.lean#L520-L534

import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedRecursion
import Definitions.Def_QEC_Locality_SeparatorProfile_Weighted
import Definitions.Def_QEC_Locality_SeparatorProfile_WeightedRefinement
import Theorems.Thm_QEC_Locality_EdgeRestrictedStoppedRecursion_edgeRegion_reverse

set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.WeightedBoundaryEdgeRecursion.edgeRegion_reverse
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary)
    (owner : tree.edgeOwnerType) (x y : ι) :
    (x, y) ∈ tree.edgeRegion owner ↔ (y, x) ∈ tree.edgeRegion owner := by sorry
