-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_step_ne_none_of_queue_ne_nil
-- name    : TunnellMap.RecordDA.step_ne_none_of_queue_ne_nil
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T16:28:40.400361+00:00
-- url     : https://prove2.me/theorems/1e50703b-b7e7-4bc5-98d4-0e4544aa37ce
-- title:
--   Record DA: step ne none of queue ne nil
-- statement:
--   The integrated machine halts only on an empty queue: it never stops
--   because a generator ran out of records.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordDeferredAcceptanceCorrect.lean#L880-L899
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordDeferredAcceptanceCorrect.lean#L880-L899

import Definitions.Def_TunnellMap_RecordDeferredAcceptance
import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen GloballyRanked
variable {n : ℤ}
variable [Fintype (BOddRep n)] [Fintype (ARep n)]

theorem TunnellMap.RecordDA.step_ne_none_of_queue_ne_nil (hn : Odd n) (hnpos : 0 < n)
    (frames : FrameFamily n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    {E : DARun n} (hSim : Sim hnpos frames E)
    (hv : (abst hn hnpos frames E).Valid (residualOrbitRanking hnpos))
    (hne : E.queue ≠ []) : step frames E ≠ none := by sorry
