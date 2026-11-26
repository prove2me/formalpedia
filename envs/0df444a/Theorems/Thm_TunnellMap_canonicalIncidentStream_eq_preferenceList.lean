-- Prove2me | Theorems.Thm_TunnellMap_canonicalIncidentStream_eq_preferenceList
-- name    : TunnellMap.canonicalIncidentStream_eq_preferenceList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:58:38.236824+00:00
-- url     : https://prove2.me/theorems/6cc939f0-3201-58ad-bb32-925ddaf33fc0
-- title:
--   Tunnell Map: canonical Incident Stream eq preference List
-- statement:
--   The Tunnell Map construction uses the canonical Incident Stream eq preference List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ResidualDeferredAcceptance.lean#L121-L132
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ResidualDeferredAcceptance.lean#L121-L132

import Definitions.Def_TunnellMap_OrderedGenerator
import Definitions.Def_TunnellMap_DeferredAcceptanceStability
import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualDeferredAcceptance
set_option autoImplicit true
open TunnellMap
open OrderedGenerator
variable {n : ℤ} [Fintype (BOddRep n)] [Fintype (ARep n)]

theorem TunnellMap.canonicalIncidentStream_eq_preferenceList
    (hn : Odd n) (hnpos : 0 < n) (hsquarefree : Squarefree n)
    (q : (bResidualInvolution n).Orbit) :
    incidentStream hnpos (canonicalBResidualRepresentative q)
        (residualSourceFrame hsquarefree
          (canonicalBResidualRepresentative q)) =
      (residualOrbitRanking hnpos).preferenceList q := by sorry
