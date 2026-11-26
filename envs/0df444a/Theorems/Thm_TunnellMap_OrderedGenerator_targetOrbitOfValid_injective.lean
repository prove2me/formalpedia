-- Prove2me | Theorems.Thm_TunnellMap_OrderedGenerator_targetOrbitOfValid_injective
-- name    : TunnellMap.OrderedGenerator.targetOrbitOfValid_injective
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:52:40.123775+00:00
-- url     : https://prove2.me/theorems/d83c733d-8749-58ee-aad4-64f2fb2a0864
-- title:
--   Ordered Generator: target Orbit Of Valid injective
-- statement:
--   The Ordered Generator construction uses the target Orbit Of Valid injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrderedGenerator.lean#L410-L423
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrderedGenerator.lean#L410-L423

import Definitions.Def_TunnellMap_GeneratorSoundness
import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_PreferenceList
import Definitions.Def_TunnellMap_OrderedGenerator
set_option autoImplicit true
open TunnellMap
open TunnellMap.OrderedGenerator
variable {n : ℤ} {p : Triple}

theorem TunnellMap.OrderedGenerator.targetOrbitOfValid_injective (hnpos : 0 < n) (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) :
    Function.Injective (targetOrbitOfValid hnpos s F) := by sorry
