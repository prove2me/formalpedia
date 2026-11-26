-- Prove2me | Theorems.Thm_TunnellMap_Examples41_preferredTarget_s2_t2
-- name    : TunnellMap.Examples41.preferredTarget_s2_t2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:46:42.999745+00:00
-- url     : https://prove2.me/theorems/3e94c6df-4bf9-49bf-892d-e80423612824
-- title:
--   Examples41: preferred Target s2 t2
-- statement:
--   The Examples41 construction uses the preferred Target s2 t2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Matching.lean#L154-L164
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Matching.lean#L154-L164

import Definitions.Def_TunnellMap_Examples41Generator
import Definitions.Def_TunnellMap_Sharpness
import Definitions.Def_TunnellMap_Examples41Matching
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
open GloballyRanked
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.preferredTarget_s2_t2 : preferredTarget s2 t2 = negAResidual t2 := by sorry
