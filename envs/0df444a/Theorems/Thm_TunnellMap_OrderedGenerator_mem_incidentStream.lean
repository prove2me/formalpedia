-- Prove2me | Theorems.Thm_TunnellMap_OrderedGenerator_mem_incidentStream
-- name    : TunnellMap.OrderedGenerator.mem_incidentStream
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:51:39.471396+00:00
-- url     : https://prove2.me/theorems/c7e32d44-266c-5f32-bfb0-b54c0a2a8d27
-- title:
--   Ordered Generator: mem incident Stream
-- statement:
--   Every residual target orbit occurs in the generated incident stream.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrderedGenerator.lean#L608-L615
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrderedGenerator.lean#L608-L615

import Definitions.Def_TunnellMap_GeneratorSoundness
import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_PreferenceList
import Definitions.Def_TunnellMap_OrderedGenerator
set_option autoImplicit true
open TunnellMap
open TunnellMap.OrderedGenerator
variable {n : ℤ} {p : Triple}

theorem TunnellMap.OrderedGenerator.mem_incidentStream (hn : Odd n) (hnpos : 0 < n)
    (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s)))
    (tOrbit : (aResidualInvolution n hnpos).Orbit) :
    tOrbit ∈ incidentStream hnpos s F := by sorry
