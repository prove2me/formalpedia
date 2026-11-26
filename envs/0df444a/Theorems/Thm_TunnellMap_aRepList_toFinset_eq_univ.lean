-- Prove2me | Theorems.Thm_TunnellMap_aRepList_toFinset_eq_univ
-- name    : TunnellMap.aRepList_toFinset_eq_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:28:09.978739+00:00
-- url     : https://prove2.me/theorems/ba0323a3-2faf-4206-a684-b16f2ff45ed5
-- title:
--   Tunnell Map: a Rep List to Finset eq univ
-- statement:
--   The Tunnell Map construction uses the a Rep List to Finset eq univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableCounting.lean#L62-L63
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableCounting.lean#L62-L63

import Definitions.Def_TunnellMap_ComputableTargetRoster
import Definitions.Def_TunnellMap_ComputableCounting
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.aRepList_toFinset_eq_univ (n : ℤ) : (aRepList n).toFinset = Finset.univ := by sorry
