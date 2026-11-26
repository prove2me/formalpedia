-- Prove2me | Theorems.Thm_TunnellMap_mem_aRepList
-- name    : TunnellMap.mem_aRepList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:27:47.551521+00:00
-- url     : https://prove2.me/theorems/f6626dc9-e7cf-5103-80ec-0a075b9f3b24
-- title:
--   Tunnell Map: mem a Rep List
-- statement:
--   The Tunnell Map construction uses the mem a Rep List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableCounting.lean#L57-L60
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableCounting.lean#L57-L60

import Definitions.Def_TunnellMap_ComputableTargetRoster
import Definitions.Def_TunnellMap_ComputableCounting
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.mem_aRepList {n : ℤ} (p : ARep n) : p ∈ aRepList n := by sorry
