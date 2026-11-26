-- Prove2me | Theorems.Thm_TunnellMap_canonicalResidualMapOf_eq_residualEquivOfOrbitCard
-- name    : TunnellMap.canonicalResidualMapOf_eq_residualEquivOfOrbitCard
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:14:37.396798+00:00
-- url     : https://prove2.me/theorems/dd18ec73-cd2c-56b0-ae2c-3dda39beee95
-- title:
--   Tunnell Map: canonical Residual Map Of eq residual Equiv Of Orbit Card
-- statement:
--   **The canonical formula agrees with the pre-existing lift.**  Even though
--   `residualEquivOfOrbitCard` was built from `Quotient.out` representatives, it
--   coincides pointwise with the manuscript's canonical sign-lift formula.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L599-L612
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L599-L612

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
variable {n : ℤ} (hnpos : 0 < n) [Fintype (BOddRep n)] [Fintype (ARep n)]

theorem TunnellMap.canonicalResidualMapOf_eq_residualEquivOfOrbitCard
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit) (x : BResidual n) :
    canonicalResidualMapOf hnpos (residualOrbitMatching hnpos hcard) x =
      residualEquivOfOrbitCard hnpos hcard x := by sorry
