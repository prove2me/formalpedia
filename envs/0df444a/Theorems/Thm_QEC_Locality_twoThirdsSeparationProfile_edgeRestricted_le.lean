-- Prove2me | Theorems.Thm_QEC_Locality_twoThirdsSeparationProfile_edgeRestricted_le
-- name    : QEC.Locality.twoThirdsSeparationProfile_edgeRestricted_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:42:08.791527+00:00
-- url     : https://prove2.me/theorems/64e9b43f-d81c-43bf-829f-1101bd8a1421
-- title:
--   Locality: two Thirds Separation Profile edge Restricted le
-- statement:
--   Exact measured profiles are inherited by finite edge restrictions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Recursion.lean#L70-L75
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Recursion.lean#L70-L75

import Definitions.Def_QEC_Locality_SeparatorProfile_EdgeDivision
import Definitions.Def_QEC_Locality_SeparatorProfile_Recursion
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.twoThirdsSeparationProfile_edgeRestricted_le
    (G : ConnectivityGraph ι) (edges : Finset (ι × ι)) (scale : Nat) :
    twoThirdsSeparationProfile (edgeRestrictedGraph G edges) scale ≤
      twoThirdsSeparationProfile G scale := by sorry
