-- Prove2me | Theorems.Thm_TunnellMap_mem_targetTriples
-- name    : TunnellMap.mem_targetTriples
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:05:36.335918+00:00
-- url     : https://prove2.me/theorems/4dae787f-53c1-5120-b6bd-3fc663f3bcab
-- title:
--   Tunnell Map: mem target Triples
-- statement:
--   The Tunnell Map construction uses the mem target Triples property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableTargetRoster.lean#L62-L74
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableTargetRoster.lean#L62-L74

import Definitions.Def_TunnellMap_ComputableRoster
import Definitions.Def_TunnellMap_ComputableTargetRoster
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.mem_targetTriples {n : ℤ} {w : Triple} (h : aForm w = n) :
    w ∈ targetTriples n := by sorry
