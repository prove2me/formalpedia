-- Prove2me | Theorems.Thm_QEC_Locality_mem_graphIsolatedVertices_iff
-- name    : QEC.Locality.mem_graphIsolatedVertices_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:06:14.578208+00:00
-- url     : https://prove2.me/theorems/f3f3ae8a-d7b0-4610-900c-66a42c2cb29d
-- title:
--   Locality: mem graph Isolated Vertices iff
-- statement:
--   The Locality construction uses the mem graph Isolated Vertices iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/EdgeDivision.lean#L171-L174
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/EdgeDivision.lean#L171-L174

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
set_option autoImplicit false
open QEC QEC.Locality
open QEC Semantics Coding
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem QEC.Locality.mem_graphIsolatedVertices_iff (G : ConnectivityGraph ι) (x : ι) :
    x ∈ graphIsolatedVertices G ↔ ∀ y, ¬ G.adjacent x y := by sorry
