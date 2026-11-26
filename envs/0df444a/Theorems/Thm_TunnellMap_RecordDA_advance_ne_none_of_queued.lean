-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_advance_ne_none_of_queued
-- name    : TunnellMap.RecordDA.advance_ne_none_of_queued
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:17:02.243438+00:00
-- url     : https://prove2.me/theorems/da16c850-8be7-4154-aecf-82c306fa4098
-- title:
--   Record DA: advance ne none of queued
-- statement:
--   **No source is ever exhausted.**  While a source is queued in a state
--   satisfying the simulation and the deferred-acceptance invariant, its
--   generator still has a record to emit.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordDeferredAcceptanceCorrect.lean#L860-L876
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordDeferredAcceptanceCorrect.lean#L860-L876

import Definitions.Def_TunnellMap_RecordDeferredAcceptance
import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen GloballyRanked
variable {n : ℤ}
variable [Fintype (BOddRep n)] [Fintype (ARep n)]

theorem TunnellMap.RecordDA.advance_ne_none_of_queued (hn : Odd n) (hnpos : 0 < n)
    (frames : FrameFamily n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    {E : DARun n} (hSim : Sim hnpos frames E)
    (hv : (abst hn hnpos frames E).Valid (residualOrbitRanking hnpos))
    (s : BResidual n) (hs : s ∈ E.queue) :
    BlockGen.advance s (frames s) (E.gen s) ≠ none := by sorry
