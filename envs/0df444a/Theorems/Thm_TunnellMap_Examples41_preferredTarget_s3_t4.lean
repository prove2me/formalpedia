-- Prove2me | Theorems.Thm_TunnellMap_Examples41_preferredTarget_s3_t4
-- name    : TunnellMap.Examples41.preferredTarget_s3_t4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:47:37.072417+00:00
-- url     : https://prove2.me/theorems/9cf40579-e4f4-4d2f-bc3a-c583640c8cb5
-- title:
--   Examples41: preferred Target s3 t4
-- statement:
--   The Examples41 construction uses the preferred Target s3 t4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Matching.lean#L166-L175
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Matching.lean#L166-L175

import Definitions.Def_TunnellMap_Examples41Generator
import Definitions.Def_TunnellMap_Sharpness
import Definitions.Def_TunnellMap_Examples41Matching
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
open GloballyRanked
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.preferredTarget_s3_t4 : preferredTarget s3 t4 = t4 := by sorry
