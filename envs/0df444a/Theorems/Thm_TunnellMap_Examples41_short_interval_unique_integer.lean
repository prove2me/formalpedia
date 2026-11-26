-- Prove2me | Theorems.Thm_TunnellMap_Examples41_short_interval_unique_integer
-- name    : TunnellMap.Examples41.short_interval_unique_integer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:08:05.294156+00:00
-- url     : https://prove2.me/theorems/32260bcb-61d8-45c5-9c6a-c7b9431b3904
-- title:
--   Examples41: short interval unique integer
-- statement:
--   The Examples41 construction uses the short interval unique integer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Generator.lean#L58-L64
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Generator.lean#L58-L64

import Definitions.Def_TunnellMap_Examples41Residual
import Definitions.Def_TunnellMap_Examples41Generator
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
open OrderedGenerator
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.short_interval_unique_integer (b : ℤ)
    (hb : bLower 41 frame41 20 1 ≤ b ∧ b ≤ bUpper 41 frame41 20 1) :
    b = -4 := by sorry
