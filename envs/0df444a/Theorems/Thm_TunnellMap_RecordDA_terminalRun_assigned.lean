-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_terminalRun_assigned
-- name    : TunnellMap.RecordDA.terminalRun_assigned
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:04:21.012408+00:00
-- url     : https://prove2.me/theorems/731af6d8-c1e0-516a-9f3d-92524c0866fa
-- title:
--   Record DA: terminal Run assigned
-- statement:
--   Every source ends up assigned a generated record whose target is the
--   canonical lift of its partner under the structural stable matching.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordDeferredAcceptanceCorrect.lean#L941-L965
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordDeferredAcceptanceCorrect.lean#L941-L965

import Definitions.Def_TunnellMap_RecordDeferredAcceptance
import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen GloballyRanked
variable {n : ℤ}
variable [Fintype (BOddRep n)] [Fintype (ARep n)]

theorem TunnellMap.RecordDA.terminalRun_assigned (hn : Odd n) (hnpos : 0 < n)
    (frames : FrameFamily n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (q : (bResidualInvolution n).Orbit) :
    ∃ r : IncidentRecord,
      (terminalRun frames).assigned (canonicalBResidualRepresentative q) =
          some r ∧
        r.target =
          orbitTargetLift hnpos (residualOrbitMatching hnpos hcard q) := by sorry
