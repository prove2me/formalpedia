-- Prove2me | Theorems.Thm_QEC_Locality_totalEdgeRegion_sharedBoundary_eq_empty
-- name    : QEC.Locality.totalEdgeRegion_sharedBoundary_eq_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:15:25.811208+00:00
-- url     : https://prove2.me/theorems/463acdad-1dd6-4cbc-9ee1-a4e292fc56cd
-- title:
--   Locality: total Edge Region shared Boundary eq empty
-- statement:
--   A one-region division has no shared boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/EdgeDivision.lean#L259-L263
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/EdgeDivision.lean#L259-L263

import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
import Definitions.Def_QEC_Locality_SeparatorProfile_EdgeDivision
set_option autoImplicit false
open QEC QEC.Locality
universe u w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.totalEdgeRegion_sharedBoundary_eq_empty (G : ConnectivityGraph ι) :
    edgeDivisionSharedBoundary (totalEdgeRegion G) totalEdgeActive = ∅ := by sorry
