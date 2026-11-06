-- Prove2me | Theorems.Thm_QEC_Locality_WeightedBoundaryEdgeRecursion_edgeOwnerType_card_eq_terminalOwnerCount
-- name    : QEC.Locality.WeightedBoundaryEdgeRecursion.edgeOwnerType_card_eq_terminalOwnerCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:43:06.774211+00:00
-- url     : https://prove2.me/theorems/1978e25f-4af7-4437-9c72-3ef6019ca964
-- title:
--   Weighted Boundary Edge Recursion: edge Owner Type card eq terminal Owner Count
-- statement:
--   The Weighted Boundary Edge Recursion construction uses the edge Owner Type card eq terminal Owner Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/WeightedRefinement.lean#L1119-L1130
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/WeightedRefinement.lean#L1119-L1130

import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedRecursion
import Definitions.Def_QEC_Locality_SeparatorProfile_Weighted
import Definitions.Def_QEC_Locality_SeparatorProfile_WeightedRefinement
import Theorems.Thm_QEC_Locality_EdgeRestrictedStoppedRecursion_edgeOwnerType_card_eq_terminalOwnerCount

set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.WeightedBoundaryEdgeRecursion.edgeOwnerType_card_eq_terminalOwnerCount
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary) :
    Fintype.card tree.edgeOwnerType = tree.terminalOwnerCount := by sorry
