-- Prove2me | Theorems.Thm_QEC_Locality_canonicalEdgeRegions_isEdgeDivision
-- name    : QEC.Locality.canonicalEdgeRegions_isEdgeDivision
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:35:40.066326+00:00
-- url     : https://prove2.me/theorems/824c37c7-8ee5-4989-ba38-67049a2ec6b4
-- title:
--   Locality: canonical Edge Regions is Edge Division
-- statement:
--   The canonical representative construction is a genuine finite edge division:
--   every orientation has one owner and the reverse orientation has the same owner.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/EdgeDivision.lean#L88-L112
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/EdgeDivision.lean#L88-L112

import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
import Definitions.Def_QEC_Locality_SeparatorProfile_EdgeDivision
set_option autoImplicit false
open QEC QEC.Locality
universe u w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.canonicalEdgeRegions_isEdgeDivision (G : ConnectivityGraph ι) :
    IsEdgeDivision G (canonicalEdgeRegion G) (canonicalEdgeRepresentatives G) := by sorry
