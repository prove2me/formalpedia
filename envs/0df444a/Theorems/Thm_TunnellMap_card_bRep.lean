-- Prove2me | Theorems.Thm_TunnellMap_card_bRep
-- name    : TunnellMap.card_bRep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:28:11.830829+00:00
-- url     : https://prove2.me/theorems/e7dd2e2e-baf6-467d-98b9-3abe9facc9e1
-- title:
--   Tunnell Map: card b Rep
-- statement:
--   **The source cardinality is computed by the enumeration.**
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableCounting.lean#L48-L49
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableCounting.lean#L48-L49

import Definitions.Def_TunnellMap_ComputableTargetRoster
import Definitions.Def_TunnellMap_ComputableCounting
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.card_bRep (n : ℤ) : Fintype.card (BRep n) = (bRepList n).dedup.length := by sorry
