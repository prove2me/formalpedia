-- Prove2me | Theorems.Thm_TunnellMap_card_aRep
-- name    : TunnellMap.card_aRep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:27:57.432781+00:00
-- url     : https://prove2.me/theorems/9ec57ea6-d6d7-54dc-83b1-3b949050691c
-- title:
--   Tunnell Map: card a Rep
-- statement:
--   **The target cardinality is computed by the enumeration.**
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableCounting.lean#L66-L67
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableCounting.lean#L66-L67

import Definitions.Def_TunnellMap_ComputableTargetRoster
import Definitions.Def_TunnellMap_ComputableCounting
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.card_aRep (n : ℤ) : Fintype.card (ARep n) = (aRepList n).dedup.length := by sorry
