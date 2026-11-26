-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_runMatching_eq
-- name    : TunnellMap.RecordDA.runMatching_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:03:59.187745+00:00
-- url     : https://prove2.me/theorems/e1889466-4fdf-5127-93fd-fdfc2278e034
-- title:
--   Record DA: run Matching eq
-- statement:
--   **The integrated execution computes the structural stable matching.**
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordDeferredAcceptanceCorrect.lean#L929-L937
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordDeferredAcceptanceCorrect.lean#L929-L937

import Definitions.Def_TunnellMap_RecordDeferredAcceptance
import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen GloballyRanked
variable {n : ℤ}
variable [Fintype (BOddRep n)] [Fintype (ARep n)]

theorem TunnellMap.RecordDA.runMatching_eq (hn : Odd n) (hnpos : 0 < n)
    (frames : FrameFamily n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit) :
    runMatching hn hnpos frames hcard = residualOrbitMatching hnpos hcard := by sorry
