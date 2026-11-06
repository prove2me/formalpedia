-- Prove2me | Theorems.Thm_QEC_Locality_mem_edgeIncidentVertices_iff
-- name    : QEC.Locality.mem_edgeIncidentVertices_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:07:00.679101+00:00
-- url     : https://prove2.me/theorems/c16b199e-b8a6-4b72-b548-34ed51e23aec
-- title:
--   Locality: mem edge Incident Vertices iff
-- statement:
--   The Locality construction uses the mem edge Incident Vertices iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/EdgeDivision.lean#L91-L95
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/EdgeDivision.lean#L91-L95

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
set_option autoImplicit false
open QEC QEC.Locality
open QEC Semantics Coding
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
omit [Fintype ι]

theorem QEC.Locality.mem_edgeIncidentVertices_iff (edges : Finset (ι × ι)) (x : ι) :
    x ∈ edgeIncidentVertices edges ↔
      ∃ edge ∈ edges, x = edge.1 ∨ x = edge.2 := by sorry
