-- Prove2me | Theorems.Thm_TunnellMap_residualDeferredAcceptance_rerun
-- name    : TunnellMap.residualDeferredAcceptance_rerun
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:59:57.721342+00:00
-- url     : https://prove2.me/theorems/5c1c8965-a749-4219-aa7f-7b0c153e298f
-- title:
--   Tunnell Map: residual Deferred Acceptance rerun
-- statement:
--   Any complete duplicate-free rerun order produces the same orbit
--   matching.  In particular, the inverse can be regenerated without retaining a
--   proposal transcript.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ResidualDeferredAcceptance.lean#L177-L189
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ResidualDeferredAcceptance.lean#L177-L189

import Definitions.Def_TunnellMap_OrderedGenerator
import Definitions.Def_TunnellMap_DeferredAcceptanceStability
import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualDeferredAcceptance
set_option autoImplicit true
open TunnellMap
open OrderedGenerator
variable {n : ℤ} (hnpos : 0 < n)
  [Fintype (BOddRep n)] [Fintype (ARep n)]

theorem TunnellMap.residualDeferredAcceptance_rerun
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (sourceOrder : List (bResidualInvolution n).Orbit)
    (hnodup : sourceOrder.Nodup)
    (hcomplete : ∀ s, s ∈ sourceOrder) :
    GloballyRanked.DAState.deferredAcceptanceMatching
        (residualOrbitRanking hnpos) hcard sourceOrder hnodup hcomplete =
      algorithmicResidualOrbitMatching hnpos hcard := by sorry
