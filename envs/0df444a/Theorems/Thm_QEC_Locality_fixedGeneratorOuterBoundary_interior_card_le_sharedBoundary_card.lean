-- Prove2me | Theorems.Thm_QEC_Locality_fixedGeneratorOuterBoundary_interior_card_le_sharedBoundary_card
-- name    : QEC.Locality.fixedGeneratorOuterBoundary_interior_card_le_sharedBoundary_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:23:19.500814+00:00
-- url     : https://prove2.me/theorems/fe8868cd-ad69-47b2-b1b3-e2f0daabdda7
-- title:
--   Locality: fixed Generator Outer Boundary interior card le shared Boundary card
-- statement:
--   The outer-boundary cardinality is bounded by the global shared boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/EdgeDivision.lean#L254-L264
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/EdgeDivision.lean#L254-L264

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
set_option autoImplicit false
open QEC QEC.Locality
open QEC Semantics Coding
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.fixedGeneratorOuterBoundary_interior_card_le_sharedBoundary_card
    {κ : Type v} [Fintype κ] {m : Type w} [DecidableEq m]
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    {regions : m → Finset (ι × ι)} {active : Finset m}
    (hDivision : IsEdgeDivision P.fixedGeneratorInteractionGraph regions active)
    {i : m} (hi : i ∈ active) :
    (fixedGeneratorOuterBoundaryFinset P
      (edgeDivisionInterior regions active i)).card ≤
        (edgeDivisionSharedBoundary regions active).card := by sorry
