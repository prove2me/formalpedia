-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_inverseByRerun_apply
-- name    : TunnellMap.RecordDA.inverseByRerun_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:07:00.958098+00:00
-- url     : https://prove2.me/theorems/31ef9a43-0e7e-4890-8cfc-b91e7a625a66
-- title:
--   Record DA: inverse By Rerun apply
-- statement:
--   The value of `inverseByRerun`, in the manuscript's notation
--   `ρ F₀ ↦ ρ η E₀`.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/InverseByRerun.lean#L200-L223
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/InverseByRerun.lean#L200-L223

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_RecordSign
import Definitions.Def_TunnellMap_InverseByRerun
set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen GloballyRanked
variable {n : ℤ}
variable [Fintype (BOddRep n)]
variable [Fintype (ARep n)]

theorem TunnellMap.RecordDA.inverseByRerun_apply (hn : Odd n) (hnpos : 0 < n)
    (frames : FrameFamily n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (fallback : BResidual n) (y : AResidual n) :
    inverseByRerun frames fallback y =
      signActB (targetLiftSign (residualTargetLift y) *
          canonicalEta hnpos
            ((residualOrbitMatching hnpos hcard).symm
              ((aResidualInvolution n hnpos).orbit y))
            ((aResidualInvolution n hnpos).orbit y))
        (canonicalBResidualRepresentative
          ((residualOrbitMatching hnpos hcard).symm
            ((aResidualInvolution n hnpos).orbit y))) := by sorry
