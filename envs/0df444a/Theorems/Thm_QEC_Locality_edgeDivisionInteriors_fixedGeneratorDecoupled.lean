-- Prove2me | Theorems.Thm_QEC_Locality_edgeDivisionInteriors_fixedGeneratorDecoupled
-- name    : QEC.Locality.edgeDivisionInteriors_fixedGeneratorDecoupled
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:15:04.27331+00:00
-- url     : https://prove2.me/theorems/57d03acf-cb94-4630-9d29-17004499502a
-- title:
--   Locality: edge Division Interiors fixed Generator Decoupled
-- statement:
--   The fixed-generator interiors of distinct regions are source-level decoupled.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/EdgeDivision.lean#L267-L284
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/EdgeDivision.lean#L267-L284

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
set_option autoImplicit false
open QEC QEC.Locality
open QEC Semantics Coding
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.edgeDivisionInteriors_fixedGeneratorDecoupled
    {κ : Type v} [Fintype κ] {m : Type w} [DecidableEq m]
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    {regions : m → Finset (ι × ι)} {active : Finset m}
    (hDivision : IsEdgeDivision P.fixedGeneratorInteractionGraph regions active)
    {i j : m} (hi : i ∈ active) (hj : j ∈ active) (hij : i ≠ j) :
    P.fixedGeneratorDecoupled
      (edgeDivisionInterior regions active i : Set ι)
      (edgeDivisionInterior regions active j : Set ι) := by sorry
