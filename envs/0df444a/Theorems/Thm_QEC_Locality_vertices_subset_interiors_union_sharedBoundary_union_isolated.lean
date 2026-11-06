-- Prove2me | Theorems.Thm_QEC_Locality_vertices_subset_interiors_union_sharedBoundary_union_isolated
-- name    : QEC.Locality.vertices_subset_interiors_union_sharedBoundary_union_isolated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:35:26.335122+00:00
-- url     : https://prove2.me/theorems/0714ae0a-00ca-44cb-93fa-de075fb9b70d
-- title:
--   Locality: vertices subset interiors union shared Boundary union isolated
-- statement:
--   All non-isolated vertices lie in an interior or in the shared boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/EdgeDivision.lean#L287-L310
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/EdgeDivision.lean#L287-L310

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
set_option autoImplicit false
open QEC QEC.Locality
open QEC Semantics Coding
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.vertices_subset_interiors_union_sharedBoundary_union_isolated
    {m : Type w} [DecidableEq m] {G : ConnectivityGraph ι}
    {regions : m → Finset (ι × ι)} {active : Finset m}
    (hDivision : IsEdgeDivision G regions active) :
    Finset.univ ⊆
      (active.biUnion fun i => edgeDivisionInterior regions active i) ∪
        edgeDivisionSharedBoundary regions active ∪ graphIsolatedVertices G := by sorry
