-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_terminalRun_held
-- name    : TunnellMap.RecordDA.terminalRun_held
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:17:02.439864+00:00
-- url     : https://prove2.me/theorems/94c618b5-5133-490a-9089-1c49e19411a4
-- title:
--   Record DA: terminal Run held
-- statement:
--   The record held at each matched target carries the proposer, the target
--   lift and the manuscript's incidence key, so the accepted sign is available
--   from the terminal state.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordDeferredAcceptanceCorrect.lean#L970-L1004
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordDeferredAcceptanceCorrect.lean#L970-L1004

import Definitions.Def_TunnellMap_RecordDeferredAcceptance
import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen GloballyRanked
variable {n : ℤ}
variable [Fintype (BOddRep n)] [Fintype (ARep n)]

theorem TunnellMap.RecordDA.terminalRun_held (hn : Odd n) (hnpos : 0 < n)
    (frames : FrameFamily n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (q : (bResidualInvolution n).Orbit) :
    ∃ r : IncidentRecord,
      (terminalRun frames).held
          (orbitTargetLift hnpos (residualOrbitMatching hnpos hcard q)) =
          some (canonicalBResidualRepresentative q, r) ∧
        r.target =
          orbitTargetLift hnpos (residualOrbitMatching hnpos hcard q) ∧
        r.key = (residualOrbitRanking hnpos).rank q
          (residualOrbitMatching hnpos hcard q) := by sorry
