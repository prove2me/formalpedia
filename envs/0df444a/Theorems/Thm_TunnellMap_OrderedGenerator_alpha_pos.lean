-- Prove2me | Theorems.Thm_TunnellMap_OrderedGenerator_alpha_pos
-- name    : TunnellMap.OrderedGenerator.alpha_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:50:02.048803+00:00
-- url     : https://prove2.me/theorems/b02b47e2-777f-515e-b008-a95095afce49
-- title:
--   Ordered Generator: alpha pos
-- statement:
--   The Ordered Generator construction uses the alpha pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrderedGenerator.lean#L164-L184
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrderedGenerator.lean#L164-L184

import Definitions.Def_TunnellMap_GeneratorSoundness
import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_PreferenceList
import Definitions.Def_TunnellMap_OrderedGenerator
set_option autoImplicit true
open TunnellMap
open TunnellMap.OrderedGenerator
variable {n : ℤ} {p : Triple}

theorem TunnellMap.OrderedGenerator.alpha_pos (F : OrthogonalFrame p) : 0 < alpha F := by sorry
