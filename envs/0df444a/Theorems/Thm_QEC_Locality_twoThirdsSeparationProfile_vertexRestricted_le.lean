-- Prove2me | Theorems.Thm_QEC_Locality_twoThirdsSeparationProfile_vertexRestricted_le
-- name    : QEC.Locality.twoThirdsSeparationProfile_vertexRestricted_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:29:05.990201+00:00
-- url     : https://prove2.me/theorems/dbe9e2eb-7852-4a54-b570-f1726045952d
-- title:
--   Locality: two Thirds Separation Profile vertex Restricted le
-- statement:
--   Exact measured profiles are inherited by ambient-type vertex restrictions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Recursion.lean#L43-L48
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Recursion.lean#L43-L48

import Definitions.Def_QEC_Locality_SeparatorProfile_EdgeDivision
import Definitions.Def_QEC_Locality_SeparatorProfile_Recursion
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.twoThirdsSeparationProfile_vertexRestricted_le
    (G : ConnectivityGraph ι) (vertices : Finset ι) (scale : Nat) :
    twoThirdsSeparationProfile (vertexRestrictedGraph G vertices) scale ≤
      twoThirdsSeparationProfile G scale := by sorry
