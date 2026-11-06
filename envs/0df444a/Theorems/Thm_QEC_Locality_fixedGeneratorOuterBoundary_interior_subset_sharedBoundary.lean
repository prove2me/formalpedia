-- Prove2me | Theorems.Thm_QEC_Locality_fixedGeneratorOuterBoundary_interior_subset_sharedBoundary
-- name    : QEC.Locality.fixedGeneratorOuterBoundary_interior_subset_sharedBoundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:35:22.686334+00:00
-- url     : https://prove2.me/theorems/46b7d187-3801-42b0-b46c-1e00ae591599
-- title:
--   Locality: fixed Generator Outer Boundary interior subset shared Boundary
-- statement:
--   Every outer neighbor of a region interior is a shared boundary vertex.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/EdgeDivision.lean#L231-L251
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/EdgeDivision.lean#L231-L251

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
set_option autoImplicit false
open QEC QEC.Locality
open QEC Semantics Coding
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.fixedGeneratorOuterBoundary_interior_subset_sharedBoundary
    {κ : Type v} [Fintype κ] {m : Type w} [DecidableEq m]
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    {regions : m → Finset (ι × ι)} {active : Finset m}
    (hDivision : IsEdgeDivision P.fixedGeneratorInteractionGraph regions active)
    {i : m} (hi : i ∈ active) :
    fixedGeneratorOuterBoundaryFinset P (edgeDivisionInterior regions active i) ⊆
      edgeDivisionSharedBoundary regions active := by sorry
