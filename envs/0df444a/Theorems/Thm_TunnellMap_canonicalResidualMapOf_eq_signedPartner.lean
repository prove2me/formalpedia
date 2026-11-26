-- Prove2me | Theorems.Thm_TunnellMap_canonicalResidualMapOf_eq_signedPartner
-- name    : TunnellMap.canonicalResidualMapOf_eq_signedPartner
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:13:48.489937+00:00
-- url     : https://prove2.me/theorems/42e9dc5f-c8d1-5714-a6c7-6e2933146d3d
-- title:
--   Tunnell Map: canonical Residual Map Of eq signed Partner
-- statement:
--   The canonical residual map is the signed partner of the matched canonical
--   target representative.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L476-L495
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L476-L495

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}

theorem TunnellMap.canonicalResidualMapOf_eq_signedPartner {n : ℤ} (hnpos : 0 < n)
    (M : (bResidualInvolution n).Orbit ≃ (aResidualInvolution n hnpos).Orbit)
    (x : BResidual n) :
    canonicalResidualMapOf hnpos M x =
      signedPartner hnpos x
        (canonicalAResidualRepresentative hnpos
          (M ((bResidualInvolution n).orbit x))) := by sorry
