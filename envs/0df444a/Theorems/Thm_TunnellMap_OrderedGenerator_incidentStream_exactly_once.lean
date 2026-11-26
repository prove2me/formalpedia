-- Prove2me | Theorems.Thm_TunnellMap_OrderedGenerator_incidentStream_exactly_once
-- name    : TunnellMap.OrderedGenerator.incidentStream_exactly_once
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:56:46.709616+00:00
-- url     : https://prove2.me/theorems/c5dcc583-91a8-4da8-8caa-9041a94db1d0
-- title:
--   Ordered Generator: incident Stream exactly once
-- statement:
--   Each residual target orbit has exactly one position in the incident
--   stream.  This is the literal exact-once assertion of Theorem 5.6.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrderedGenerator.lean#L619-L629
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrderedGenerator.lean#L619-L629

import Definitions.Def_TunnellMap_GeneratorSoundness
import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_PreferenceList
import Definitions.Def_TunnellMap_OrderedGenerator
set_option autoImplicit true
open TunnellMap
open TunnellMap.OrderedGenerator
variable {n : ℤ} {p : Triple}

theorem TunnellMap.OrderedGenerator.incidentStream_exactly_once (hn : Odd n) (hnpos : 0 < n)
    (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s)))
    (tOrbit : (aResidualInvolution n hnpos).Orbit) :
    ∃! i : Fin (incidentStream hnpos s F).length,
      (incidentStream hnpos s F).get i = tOrbit := by sorry
