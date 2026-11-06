-- Prove2me | Theorems.Thm_QEC_Locality_mem_canonicalEdgeRegion_iff
-- name    : QEC.Locality.mem_canonicalEdgeRegion_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:15:05.29037+00:00
-- url     : https://prove2.me/theorems/4d1845d1-38e1-4d03-9d5d-c816b09fc1a9
-- title:
--   Locality: mem canonical Edge Region iff
-- statement:
--   The Locality construction uses the mem canonical Edge Region iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/EdgeDivision.lean#L77-L82
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/EdgeDivision.lean#L77-L82

import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
import Definitions.Def_QEC_Locality_SeparatorProfile_EdgeDivision
set_option autoImplicit false
open QEC QEC.Locality
universe u w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.mem_canonicalEdgeRegion_iff (G : ConnectivityGraph ι)
    (owner edge : ι × ι) :
    edge ∈ canonicalEdgeRegion G owner ↔
      edge ∈ directedEdgeFinset G ∧ canonicalEdgeOwner edge = owner := by sorry
