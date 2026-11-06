-- Prove2me | Theorems.Thm_QEC_Locality_edgeDivision_regions_pairwise_disjoint
-- name    : QEC.Locality.edgeDivision_regions_pairwise_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:22:11.305996+00:00
-- url     : https://prove2.me/theorems/ae9e5845-2d29-4d1a-9166-276e4923acb1
-- title:
--   Locality: edge Division regions pairwise disjoint
-- statement:
--   Distinct active regions have disjoint edge sets.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/EdgeDivision.lean#L128-L140
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/EdgeDivision.lean#L128-L140

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
set_option autoImplicit false
open QEC QEC.Locality
open QEC Semantics Coding
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem QEC.Locality.edgeDivision_regions_pairwise_disjoint {m : Type w} [DecidableEq m]
    {G : ConnectivityGraph ι} {regions : m → Finset (ι × ι)}
    {active : Finset m} (hDivision : IsEdgeDivision G regions active)
    {i j : m} (hi : i ∈ active) (hj : j ∈ active) (hij : i ≠ j) :
    Disjoint (regions i) (regions j) := by sorry
