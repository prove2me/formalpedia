-- Prove2me | Theorems.Thm_QEC_Locality_mem_edgeDivisionSharedBoundary_iff
-- name    : QEC.Locality.mem_edgeDivisionSharedBoundary_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:06:37.14804+00:00
-- url     : https://prove2.me/theorems/c1902ff8-41f6-4b4f-b46e-a20b6cdbf775
-- title:
--   Locality: mem edge Division Shared Boundary iff
-- statement:
--   The Locality construction uses the mem edge Division Shared Boundary iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/EdgeDivision.lean#L151-L158
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/EdgeDivision.lean#L151-L158

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
set_option autoImplicit false
open QEC QEC.Locality
open QEC Semantics Coding
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.mem_edgeDivisionSharedBoundary_iff {m : Type w} [DecidableEq m]
    (regions : m → Finset (ι × ι)) (active : Finset m) (x : ι) :
    x ∈ edgeDivisionSharedBoundary regions active ↔
      ∃ i ∈ active, ∃ j ∈ active, i ≠ j ∧
        x ∈ edgeIncidentVertices (regions i) ∧
        x ∈ edgeIncidentVertices (regions j) := by sorry
