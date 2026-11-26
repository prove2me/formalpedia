-- Prove2me | Theorems.Thm_TunnellMap_OrderedGenerator_exists_validIndex_for_targetOrbit
-- name    : TunnellMap.OrderedGenerator.exists_validIndex_for_targetOrbit
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:54:10.54734+00:00
-- url     : https://prove2.me/theorems/ec344e97-c3f6-4399-b62e-7002966e21f2
-- title:
--   Ordered Generator: exists valid Index for target Orbit
-- statement:
--   Completeness of the nested arithmetic loops: every residual target orbit
--   occurs among the retained indices for every oriented source frame.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrderedGenerator.lean#L504-L605
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrderedGenerator.lean#L504-L605

import Definitions.Def_TunnellMap_GeneratorSoundness
import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_PreferenceList
import Definitions.Def_TunnellMap_OrderedGenerator
set_option autoImplicit true
open TunnellMap
open TunnellMap.OrderedGenerator
variable {n : ℤ} {p : Triple}

theorem TunnellMap.OrderedGenerator.exists_validIndex_for_targetOrbit (hn : Odd n) (hnpos : 0 < n)
    (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s)))
    (tOrbit : (aResidualInvolution n hnpos).Orbit) :
    ∃ i : {i // i ∈ validIndices s F},
      targetOrbitOfValid hnpos s F i = tOrbit := by sorry
