-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_terminalRun_held_sign
-- name    : TunnellMap.RecordDA.terminalRun_held_sign
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:09:25.000987+00:00
-- url     : https://prove2.me/theorems/495fc0aa-a2f3-4a5e-a8ad-8c5792363e64
-- title:
--   Record DA: terminal Run held sign
-- statement:
--   **The terminal state stores the canonical edge sign.**  For every residual
--   source orbit `q`, the target orbit matched to `q` holds a record proposed by
--   the canonical representative of `q` whose stored sign is the manuscript's
--   canonical edge sign `η`.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/InverseByRerun.lean#L122-L142
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/InverseByRerun.lean#L122-L142

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_RecordSign
import Definitions.Def_TunnellMap_InverseByRerun
set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen GloballyRanked
variable {n : ℤ}
variable [Fintype (BOddRep n)] [Fintype (ARep n)]

theorem TunnellMap.RecordDA.terminalRun_held_sign (hn : Odd n) (hnpos : 0 < n)
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
        r.sign =
          canonicalEta hnpos q (residualOrbitMatching hnpos hcard q) := by sorry
