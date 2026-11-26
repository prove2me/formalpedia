-- Prove2me | Theorems.Thm_TunnellMap_incidentStream_pairwise
-- name    : TunnellMap.incidentStream_pairwise
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:59:18.730743+00:00
-- url     : https://prove2.me/theorems/fa4ead72-d4b5-5ab3-a8ee-ef65db6f0809
-- title:
--   Tunnell Map: incident Stream pairwise
-- statement:
--   The generated arithmetic stream is pairwise ordered by the same global
--   projective key as the abstract preference list.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ResidualDeferredAcceptance.lean#L72-L81
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ResidualDeferredAcceptance.lean#L72-L81

import Definitions.Def_TunnellMap_OrderedGenerator
import Definitions.Def_TunnellMap_DeferredAcceptanceStability
import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualDeferredAcceptance
set_option autoImplicit true
open TunnellMap
open OrderedGenerator
variable {n : ℤ} [Fintype (BOddRep n)] [Fintype (ARep n)]

theorem TunnellMap.incidentStream_pairwise (hnpos : 0 < n) (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) :
    (incidentStream hnpos s F).Pairwise fun t₁ t₂ =>
      (residualOrbitRanking hnpos).rank
          ((bResidualInvolution n).orbit s) t₁ ≤
        (residualOrbitRanking hnpos).rank
          ((bResidualInvolution n).orbit s) t₂ := by sorry
