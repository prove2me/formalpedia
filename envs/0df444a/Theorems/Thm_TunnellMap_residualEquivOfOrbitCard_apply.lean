-- Prove2me | Theorems.Thm_TunnellMap_residualEquivOfOrbitCard_apply
-- name    : TunnellMap.residualEquivOfOrbitCard_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:16:16.760495+00:00
-- url     : https://prove2.me/theorems/76225f42-0989-4e2c-a18b-608420fbdfe1
-- title:
--   Tunnell Map: residual Equiv Of Orbit Card apply
-- statement:
--   The pre-existing lifted equivalence, evaluated at an arbitrary point, is
--   the signed partner of the `Quotient.out` representative of the matched target
--   orbit.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L573-L594
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L573-L594

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
variable {n : ℤ} (hnpos : 0 < n) [Fintype (BOddRep n)] [Fintype (ARep n)]

theorem TunnellMap.residualEquivOfOrbitCard_apply
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit) (x : BResidual n) :
    residualEquivOfOrbitCard hnpos hcard x =
      signedPartner hnpos x
        ((aResidualInvolution n hnpos).representative
          (residualOrbitMatching hnpos hcard
            ((bResidualInvolution n).orbit x))) := by sorry
