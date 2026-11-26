-- Prove2me | Theorems.Thm_TunnellMap_mem_bRepList
-- name    : TunnellMap.mem_bRepList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:15:18.849713+00:00
-- url     : https://prove2.me/theorems/3642b6c3-50e2-554b-b4c8-6aba950cc838
-- title:
--   Tunnell Map: mem b Rep List
-- statement:
--   The Tunnell Map construction uses the mem b Rep List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableCounting.lean#L39-L42
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableCounting.lean#L39-L42

import Definitions.Def_TunnellMap_ComputableTargetRoster
import Definitions.Def_TunnellMap_ComputableCounting
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.mem_bRepList {n : ℤ} (p : BRep n) : p ∈ bRepList n := by sorry
