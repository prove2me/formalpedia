-- Prove2me | Theorems.Thm_QEC_Locality_edgeDivisionInteriors_disjoint
-- name    : QEC.Locality.edgeDivisionInteriors_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:35:14.344925+00:00
-- url     : https://prove2.me/theorems/8c5a2c34-3a4c-4945-90df-657c903d81f3
-- title:
--   Locality: edge Division Interiors disjoint
-- statement:
--   Distinct edge-region interiors are vertex-disjoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/EdgeDivision.lean#L177-L188
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/EdgeDivision.lean#L177-L188

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
set_option autoImplicit false
open QEC QEC.Locality
open QEC Semantics Coding
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.edgeDivisionInteriors_disjoint {m : Type w} [DecidableEq m]
    (regions : m → Finset (ι × ι)) (active : Finset m)
    {i j : m} (hi : i ∈ active) (hj : j ∈ active) (hij : i ≠ j) :
    Disjoint (edgeDivisionInterior regions active i)
      (edgeDivisionInterior regions active j) := by sorry
