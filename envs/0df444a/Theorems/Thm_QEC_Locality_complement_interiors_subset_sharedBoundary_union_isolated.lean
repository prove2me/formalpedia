-- Prove2me | Theorems.Thm_QEC_Locality_complement_interiors_subset_sharedBoundary_union_isolated
-- name    : QEC.Locality.complement_interiors_subset_sharedBoundary_union_isolated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:35:34.446695+00:00
-- url     : https://prove2.me/theorems/2be851ab-8cc1-437e-a49f-6c75b522aaef
-- title:
--   Locality: complement interiors subset shared Boundary union isolated
-- statement:
--   Removing all interiors leaves only shared-boundary and isolated vertices.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/EdgeDivision.lean#L313-L326
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/EdgeDivision.lean#L313-L326

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
set_option autoImplicit false
open QEC QEC.Locality
open QEC Semantics Coding
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.complement_interiors_subset_sharedBoundary_union_isolated
    {m : Type w} [DecidableEq m] {G : ConnectivityGraph ι}
    {regions : m → Finset (ι × ι)} {active : Finset m}
    (hDivision : IsEdgeDivision G regions active) :
    Finset.univ \ (active.biUnion fun i => edgeDivisionInterior regions active i) ⊆
      edgeDivisionSharedBoundary regions active ∪ graphIsolatedVertices G := by sorry
