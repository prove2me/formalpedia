-- Prove2me | Theorems.Thm_TunnellMap_Examples41_preferredTarget_s4_t3
-- name    : TunnellMap.Examples41.preferredTarget_s4_t3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:48:18.810185+00:00
-- url     : https://prove2.me/theorems/f6a9fd59-eb44-48e2-89d9-4d4495ea519c
-- title:
--   Examples41: preferred Target s4 t3
-- statement:
--   The Examples41 construction uses the preferred Target s4 t3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Matching.lean#L177-L186
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Matching.lean#L177-L186

import Definitions.Def_TunnellMap_Examples41Generator
import Definitions.Def_TunnellMap_Sharpness
import Definitions.Def_TunnellMap_Examples41Matching
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
open GloballyRanked
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.preferredTarget_s4_t3 : preferredTarget s4 t3 = t3 := by sorry
