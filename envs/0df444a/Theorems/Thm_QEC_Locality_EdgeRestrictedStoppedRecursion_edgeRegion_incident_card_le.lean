-- Prove2me | Theorems.Thm_QEC_Locality_EdgeRestrictedStoppedRecursion_edgeRegion_incident_card_le
-- name    : QEC.Locality.EdgeRestrictedStoppedRecursion.edgeRegion_incident_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:17:15.470187+00:00
-- url     : https://prove2.me/theorems/c695fc23-5455-462a-8104-6ae477d9c052
-- title:
--   Edge Restricted Stopped Recursion: edge Region incident card le
-- statement:
--   A terminal stopped-recursion region obeys the requested incident cap.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/StoppedRecursion.lean#L382-L394
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/StoppedRecursion.lean#L382-L394

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedRecursion
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.EdgeRestrictedStoppedRecursion.edgeRegion_incident_card_le
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (owner : tree.edgeOwnerType) :
    (edgeIncidentVertices (tree.edgeRegion owner)).card ≤ r := by sorry
