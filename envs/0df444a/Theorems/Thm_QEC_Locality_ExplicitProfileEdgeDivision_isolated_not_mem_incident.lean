-- Prove2me | Theorems.Thm_QEC_Locality_ExplicitProfileEdgeDivision_isolated_not_mem_incident
-- name    : QEC.Locality.ExplicitProfileEdgeDivision.isolated_not_mem_incident
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:01:12.349463+00:00
-- url     : https://prove2.me/theorems/c802c52d-a7e8-401e-8a00-f1d473d84e20
-- title:
--   Explicit Profile Edge Division: isolated not mem incident
-- statement:
--   Graph-isolated vertices are incident to no active edge region.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/ExplicitDivision.lean#L217-L232
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/ExplicitDivision.lean#L217-L232

import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedPotential
import Definitions.Def_QEC_Locality_SeparatorProfile_ExplicitDivision
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.ExplicitProfileEdgeDivision.isolated_not_mem_incident
    {G : ConnectivityGraph ι} {incidentCap localBoundaryCap activeCountCap : Nat}
    (division : ExplicitProfileEdgeDivision G incidentCap localBoundaryCap activeCountCap)
    {x : ι} (hx : x ∈ graphIsolatedVertices G)
    (owner : division.Owner) (howner : owner ∈ division.active) :
    x ∉ edgeIncidentVertices (division.region owner) := by sorry
