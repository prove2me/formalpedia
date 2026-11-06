-- Prove2me | Theorems.Thm_QEC_Locality_mem_directedEdgeFinset_iff
-- name    : QEC.Locality.mem_directedEdgeFinset_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:07:05.734247+00:00
-- url     : https://prove2.me/theorems/27389719-8412-442a-b9cd-fb735014aa01
-- title:
--   Locality: mem directed Edge Finset iff
-- statement:
--   The Locality construction uses the mem directed Edge Finset iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/EdgeDivision.lean#L81-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/EdgeDivision.lean#L81-L84

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
set_option autoImplicit false
open QEC QEC.Locality
open QEC Semantics Coding
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem QEC.Locality.mem_directedEdgeFinset_iff (G : ConnectivityGraph ι) (x y : ι) :
    (x, y) ∈ directedEdgeFinset G ↔ G.adjacent x y := by sorry
