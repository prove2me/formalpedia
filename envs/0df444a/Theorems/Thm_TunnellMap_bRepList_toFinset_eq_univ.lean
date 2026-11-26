-- Prove2me | Theorems.Thm_TunnellMap_bRepList_toFinset_eq_univ
-- name    : TunnellMap.bRepList_toFinset_eq_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:27:29.523306+00:00
-- url     : https://prove2.me/theorems/e9234148-9ec1-5755-8e6f-0b3b92e2c6c9
-- title:
--   Tunnell Map: b Rep List to Finset eq univ
-- statement:
--   The Tunnell Map construction uses the b Rep List to Finset eq univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableCounting.lean#L44-L45
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableCounting.lean#L44-L45

import Definitions.Def_TunnellMap_ComputableTargetRoster
import Definitions.Def_TunnellMap_ComputableCounting
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.bRepList_toFinset_eq_univ (n : ℤ) : (bRepList n).toFinset = Finset.univ := by sorry
