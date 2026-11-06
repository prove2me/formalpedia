-- Prove2me | Theorems.Thm_QEC_Locality_emptyEdgeRegion_sharedBoundary_eq_empty
-- name    : QEC.Locality.emptyEdgeRegion_sharedBoundary_eq_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:24:58.468238+00:00
-- url     : https://prove2.me/theorems/982ca52e-6f54-4e18-aac4-4c512c01b5a9
-- title:
--   Locality: empty Edge Region shared Boundary eq empty
-- statement:
--   The zero-region edgeless wrapper also has empty shared boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/EdgeDivision.lean#L281-L285
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/EdgeDivision.lean#L281-L285

import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
import Definitions.Def_QEC_Locality_SeparatorProfile_EdgeDivision
set_option autoImplicit false
open QEC QEC.Locality
universe u w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.emptyEdgeRegion_sharedBoundary_eq_empty :
    edgeDivisionSharedBoundary (emptyEdgeRegion (ι := ι)) emptyEdgeActive = ∅ := by sorry
