-- Prove2me | Theorems.Thm_TunnellMap_OrderedGenerator_incidentStream_key_strict
-- name    : TunnellMap.OrderedGenerator.incidentStream_key_strict
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:56:00.795624+00:00
-- url     : https://prove2.me/theorems/1974680a-03d4-4455-ad6a-520d70f2ea4f
-- title:
--   Ordered Generator: incident Stream key strict
-- statement:
--   The emitted incident orbits occur in strictly increasing projective-key
--   order.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrderedGenerator.lean#L634-L662
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrderedGenerator.lean#L634-L662

import Definitions.Def_TunnellMap_GeneratorSoundness
import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_PreferenceList
import Definitions.Def_TunnellMap_OrderedGenerator
set_option autoImplicit true
open TunnellMap
open TunnellMap.OrderedGenerator
variable {n : ℤ} {p : Triple}
set_option maxHeartbeats 800000

theorem TunnellMap.OrderedGenerator.incidentStream_key_strict (hnpos : 0 < n)
    (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s)))
    {i j : Fin (incidentStream hnpos s F).length} (hij : i < j) :
    orbitEdgeKey hnpos ((bResidualInvolution n).orbit s)
        ((incidentStream hnpos s F).get i) <
      orbitEdgeKey hnpos ((bResidualInvolution n).orbit s)
        ((incidentStream hnpos s F).get j) := by sorry
