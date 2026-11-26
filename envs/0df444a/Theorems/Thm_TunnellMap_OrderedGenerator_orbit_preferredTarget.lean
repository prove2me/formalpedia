-- Prove2me | Theorems.Thm_TunnellMap_OrderedGenerator_orbit_preferredTarget
-- name    : TunnellMap.OrderedGenerator.orbit_preferredTarget
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:55:24.387688+00:00
-- url     : https://prove2.me/theorems/960b1bdf-9b72-4ae4-9385-e6b174f98cfe
-- title:
--   Ordered Generator: orbit preferred Target
-- statement:
--   The Ordered Generator construction uses the orbit preferred Target property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrderedGenerator.lean#L487-L494
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrderedGenerator.lean#L487-L494

import Definitions.Def_TunnellMap_GeneratorSoundness
import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_PreferenceList
import Definitions.Def_TunnellMap_OrderedGenerator
set_option autoImplicit true
open TunnellMap
open TunnellMap.OrderedGenerator
variable {n : ℤ} {p : Triple}

theorem TunnellMap.OrderedGenerator.orbit_preferredTarget (hnpos : 0 < n) (s : BResidual n)
    (t : AResidual n) :
    (aResidualInvolution n hnpos).orbit (preferredTarget s t) =
      (aResidualInvolution n hnpos).orbit t := by sorry
