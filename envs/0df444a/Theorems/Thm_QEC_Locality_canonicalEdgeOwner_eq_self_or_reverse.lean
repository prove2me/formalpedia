-- Prove2me | Theorems.Thm_QEC_Locality_canonicalEdgeOwner_eq_self_or_reverse
-- name    : QEC.Locality.canonicalEdgeOwner_eq_self_or_reverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:35:49.542284+00:00
-- url     : https://prove2.me/theorems/e35fc915-e7e4-43bd-a33a-7755c2c083cb
-- title:
--   Locality: canonical Edge Owner eq self or reverse
-- statement:
--   The Locality construction uses the canonical Edge Owner eq self or reverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/EdgeDivision.lean#L41-L46
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/EdgeDivision.lean#L41-L46

import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
import Definitions.Def_QEC_Locality_SeparatorProfile_EdgeDivision
set_option autoImplicit false
open QEC QEC.Locality
universe u w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem QEC.Locality.canonicalEdgeOwner_eq_self_or_reverse (edge : ι × ι) :
    canonicalEdgeOwner edge = edge ∨
      canonicalEdgeOwner edge = reverseDirectedEdge edge := by sorry
