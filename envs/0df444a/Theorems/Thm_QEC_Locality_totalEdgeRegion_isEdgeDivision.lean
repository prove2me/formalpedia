-- Prove2me | Theorems.Thm_QEC_Locality_totalEdgeRegion_isEdgeDivision
-- name    : QEC.Locality.totalEdgeRegion_isEdgeDivision
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:15:08.493486+00:00
-- url     : https://prove2.me/theorems/b8802eb5-ae9e-4a4e-bd08-8bd995e4a6a7
-- title:
--   Locality: total Edge Region is Edge Division
-- statement:
--   The Locality construction uses the total Edge Region is Edge Division property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/EdgeDivision.lean#L194-L210
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/EdgeDivision.lean#L194-L210

import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
import Definitions.Def_QEC_Locality_SeparatorProfile_EdgeDivision
set_option autoImplicit false
open QEC QEC.Locality
universe u w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem QEC.Locality.totalEdgeRegion_isEdgeDivision (G : ConnectivityGraph ι) :
    IsEdgeDivision G (totalEdgeRegion G) totalEdgeActive := by sorry
