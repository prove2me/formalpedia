-- Prove2me | Theorems.Thm_TunnellMap_incidentStream_eq_preferenceList
-- name    : TunnellMap.incidentStream_eq_preferenceList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:57:32.381452+00:00
-- url     : https://prove2.me/theorems/288c84c0-2dd1-4e53-a73a-ce5f55b72754
-- title:
--   Tunnell Map: incident Stream eq preference List
-- statement:
--   The arithmetic generator and the abstract finite sort define literally
--   the same preference list.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ResidualDeferredAcceptance.lean#L85-L107
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ResidualDeferredAcceptance.lean#L85-L107

import Definitions.Def_TunnellMap_OrderedGenerator
import Definitions.Def_TunnellMap_DeferredAcceptanceStability
import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualDeferredAcceptance
set_option autoImplicit true
open TunnellMap
open OrderedGenerator
variable {n : ℤ} [Fintype (BOddRep n)] [Fintype (ARep n)]

theorem TunnellMap.incidentStream_eq_preferenceList (hn : Odd n) (hnpos : 0 < n)
    (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) :
    incidentStream hnpos s F =
      (residualOrbitRanking hnpos).preferenceList
        ((bResidualInvolution n).orbit s) := by sorry
