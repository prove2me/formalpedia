-- Prove2me | Theorems.Thm_QEC_Locality_canonicalEdgeRegion_localSharedBoundary_card_le_two
-- name    : QEC.Locality.canonicalEdgeRegion_localSharedBoundary_card_le_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:35:51.739622+00:00
-- url     : https://prove2.me/theorems/6fdb9b78-9eba-4cc0-b017-d1589d966106
-- title:
--   Locality: canonical Edge Region local Shared Boundary card le two
-- statement:
--   The local shared boundary of a canonical leaf is also at most two.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/EdgeDivision.lean#L146-L153
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/EdgeDivision.lean#L146-L153

import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
import Definitions.Def_QEC_Locality_SeparatorProfile_EdgeDivision
set_option autoImplicit false
open QEC QEC.Locality
universe u w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.canonicalEdgeRegion_localSharedBoundary_card_le_two
    (G : ConnectivityGraph ι) (owner : ι × ι) :
    ((edgeIncidentVertices (canonicalEdgeRegion G owner)) ∩
      edgeDivisionSharedBoundary (canonicalEdgeRegion G)
        (canonicalEdgeRepresentatives G)).card ≤ 2 := by sorry
