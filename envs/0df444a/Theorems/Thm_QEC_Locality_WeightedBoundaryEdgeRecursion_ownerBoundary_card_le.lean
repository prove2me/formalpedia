-- Prove2me | Theorems.Thm_QEC_Locality_WeightedBoundaryEdgeRecursion_ownerBoundary_card_le
-- name    : QEC.Locality.WeightedBoundaryEdgeRecursion.ownerBoundary_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:42:46.985518+00:00
-- url     : https://prove2.me/theorems/aff380a5-47ae-4933-b918-096b96fce5df
-- title:
--   Weighted Boundary Edge Recursion: owner Boundary card le
-- statement:
--   The Weighted Boundary Edge Recursion construction uses the owner Boundary card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/WeightedRefinement.lean#L553-L567
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/WeightedRefinement.lean#L553-L567

import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedRecursion
import Definitions.Def_QEC_Locality_SeparatorProfile_Weighted
import Definitions.Def_QEC_Locality_SeparatorProfile_WeightedRefinement
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.WeightedBoundaryEdgeRecursion.ownerBoundary_card_le
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary)
    (owner : tree.edgeOwnerType) :
    (tree.ownerBoundary owner).card ≤ 6 * spineBudget := by sorry
