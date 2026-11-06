-- Prove2me | Theorems.Thm_QEC_Locality_canonicalEdgeOwner_reverse
-- name    : QEC.Locality.canonicalEdgeOwner_reverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:36:37.618928+00:00
-- url     : https://prove2.me/theorems/2638ba57-c5f4-4880-82e8-eda28c6755d0
-- title:
--   Locality: canonical Edge Owner reverse
-- statement:
--   Reversing an oriented pair does not change its canonical owner.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/EdgeDivision.lean#L50-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/EdgeDivision.lean#L50-L65

import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
import Definitions.Def_QEC_Locality_SeparatorProfile_EdgeDivision
set_option autoImplicit false
open QEC QEC.Locality
universe u w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem QEC.Locality.canonicalEdgeOwner_reverse (edge : ι × ι) :
    canonicalEdgeOwner (reverseDirectedEdge edge) = canonicalEdgeOwner edge := by sorry
