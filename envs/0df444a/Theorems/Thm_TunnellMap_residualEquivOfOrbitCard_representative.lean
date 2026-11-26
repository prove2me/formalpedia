-- Prove2me | Theorems.Thm_TunnellMap_residualEquivOfOrbitCard_representative
-- name    : TunnellMap.residualEquivOfOrbitCard_representative
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:03:20.792669+00:00
-- url     : https://prove2.me/theorems/926dc286-73e2-4ba7-b490-b45314f304b6
-- title:
--   Tunnell Map: residual Equiv Of Orbit Card representative
-- statement:
--   On a chosen source representative, the residual equivalence is precisely
--   the preferred signed lift of the stable orbit edge.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrbitLift.lean#L122-L147
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrbitLift.lean#L122-L147

import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_Assembly
import Definitions.Def_TunnellMap_OrbitLift
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.residualEquivOfOrbitCard_representative {n : ℤ} (hnpos : 0 < n)
    [Fintype (BOddRep n)] [Fintype (ARep n)]
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (s : (bResidualInvolution n).Orbit) :
    residualEquivOfOrbitCard hnpos hcard
        ((bResidualInvolution n).representative s) =
      preferredTarget ((bResidualInvolution n).representative s)
        ((aResidualInvolution n hnpos).representative
          (residualOrbitMatching hnpos hcard s)) := by sorry
