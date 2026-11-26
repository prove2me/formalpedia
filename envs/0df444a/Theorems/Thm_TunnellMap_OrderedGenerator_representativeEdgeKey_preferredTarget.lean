-- Prove2me | Theorems.Thm_TunnellMap_OrderedGenerator_representativeEdgeKey_preferredTarget
-- name    : TunnellMap.OrderedGenerator.representativeEdgeKey_preferredTarget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:53:32.122363+00:00
-- url     : https://prove2.me/theorems/8601062c-4288-5d13-af56-f5993839b67b
-- title:
--   Ordered Generator: representative Edge Key preferred Target
-- statement:
--   The Ordered Generator construction uses the representative Edge Key preferred Target property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrderedGenerator.lean#L496-L500
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrderedGenerator.lean#L496-L500

import Definitions.Def_TunnellMap_GeneratorSoundness
import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_PreferenceList
import Definitions.Def_TunnellMap_OrderedGenerator
set_option autoImplicit true
open TunnellMap
open TunnellMap.OrderedGenerator
variable {n : ℤ} {p : Triple}

theorem TunnellMap.OrderedGenerator.representativeEdgeKey_preferredTarget (s : BResidual n)
    (t : AResidual n) :
    representativeEdgeKey s (preferredTarget s t) = representativeEdgeKey s t := by sorry
