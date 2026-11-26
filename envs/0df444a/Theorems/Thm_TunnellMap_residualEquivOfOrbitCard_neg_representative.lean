-- Prove2me | Theorems.Thm_TunnellMap_residualEquivOfOrbitCard_neg_representative
-- name    : TunnellMap.residualEquivOfOrbitCard_neg_representative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:14:32.282828+00:00
-- url     : https://prove2.me/theorems/71e8847e-3dc8-414f-a9eb-08b8b46decb1
-- title:
--   Tunnell Map: residual Equiv Of Orbit Card neg representative
-- statement:
--   The pre-existing lifted equivalence at the antipode of the chosen source
--   representative.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L524-L568
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L524-L568

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
variable {n : ℤ} (hnpos : 0 < n) [Fintype (BOddRep n)] [Fintype (ARep n)]

theorem TunnellMap.residualEquivOfOrbitCard_neg_representative
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (q : (bResidualInvolution n).Orbit) :
    residualEquivOfOrbitCard hnpos hcard
        (negBResidual ((bResidualInvolution n).representative q)) =
      negAResidual
        (preferredTarget ((bResidualInvolution n).representative q)
          ((aResidualInvolution n hnpos).representative
            (residualOrbitMatching hnpos hcard q))) := by sorry
