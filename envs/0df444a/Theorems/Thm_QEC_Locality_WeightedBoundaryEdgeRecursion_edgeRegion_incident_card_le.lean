-- Prove2me | Theorems.Thm_QEC_Locality_WeightedBoundaryEdgeRecursion_edgeRegion_incident_card_le
-- name    : QEC.Locality.WeightedBoundaryEdgeRecursion.edgeRegion_incident_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:43:23.323226+00:00
-- url     : https://prove2.me/theorems/e53db20d-121d-42bb-8e3a-c18bef84ff88
-- title:
--   Weighted Boundary Edge Recursion: edge Region incident card le
-- statement:
--   The Weighted Boundary Edge Recursion construction uses the edge Region incident card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/WeightedRefinement.lean#L536-L551
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/WeightedRefinement.lean#L536-L551

import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedRecursion
import Definitions.Def_QEC_Locality_SeparatorProfile_Weighted
import Definitions.Def_QEC_Locality_SeparatorProfile_WeightedRefinement
import Theorems.Thm_QEC_Locality_EdgeRestrictedStoppedRecursion_edgeRegion_incident_card_le

set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.WeightedBoundaryEdgeRecursion.edgeRegion_incident_card_le
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary)
    (owner : tree.edgeOwnerType) :
    (edgeIncidentVertices (tree.edgeRegion owner)).card ≤ r := by sorry
