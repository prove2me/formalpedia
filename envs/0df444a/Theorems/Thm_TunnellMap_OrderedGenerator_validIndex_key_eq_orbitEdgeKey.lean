-- Prove2me | Theorems.Thm_TunnellMap_OrderedGenerator_validIndex_key_eq_orbitEdgeKey
-- name    : TunnellMap.OrderedGenerator.validIndex_key_eq_orbitEdgeKey
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:50:09.53939+00:00
-- url     : https://prove2.me/theorems/88e83e9c-989e-5f57-9208-7f4079e8e5e9
-- title:
--   Ordered Generator: valid Index key eq orbit Edge Key
-- statement:
--   The Ordered Generator construction uses the valid Index key eq orbit Edge Key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrderedGenerator.lean#L394-L408
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrderedGenerator.lean#L394-L408

import Definitions.Def_TunnellMap_GeneratorSoundness
import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_PreferenceList
import Definitions.Def_TunnellMap_OrderedGenerator
set_option autoImplicit true
open TunnellMap
open TunnellMap.OrderedGenerator
variable {n : ℤ} {p : Triple}

theorem TunnellMap.OrderedGenerator.validIndex_key_eq_orbitEdgeKey (hnpos : 0 < n) (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s)))
    (i : {i // i ∈ validIndices s F}) :
    directionKey (dValue F i.1) =
      orbitEdgeKey hnpos ((bResidualInvolution n).orbit s)
        (targetOrbitOfValid hnpos s F i) := by sorry
