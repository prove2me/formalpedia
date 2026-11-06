-- Prove2me | Theorems.Thm_QEC_Locality_edgeDivisionInteriors_noEdgeBetween
-- name    : QEC.Locality.edgeDivisionInteriors_noEdgeBetween
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:35:20.751467+00:00
-- url     : https://prove2.me/theorems/1ee104f3-4631-4473-a729-fa62e04e0285
-- title:
--   Locality: edge Division Interiors no Edge Between
-- statement:
--   Different interiors have no edge between them in the divided graph.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/EdgeDivision.lean#L214-L228
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/EdgeDivision.lean#L214-L228

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
set_option autoImplicit false
open QEC QEC.Locality
open QEC Semantics Coding
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.edgeDivisionInteriors_noEdgeBetween {m : Type w} [DecidableEq m]
    {G : ConnectivityGraph ι} {regions : m → Finset (ι × ι)}
    {active : Finset m} (hDivision : IsEdgeDivision G regions active)
    {i j : m} (hi : i ∈ active) (hj : j ∈ active) (hij : i ≠ j) :
    NoEdgeBetween G (edgeDivisionInterior regions active i)
      (edgeDivisionInterior regions active j) := by sorry
