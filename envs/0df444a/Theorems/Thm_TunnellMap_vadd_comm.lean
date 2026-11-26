-- Prove2me | Theorems.Thm_TunnellMap_vadd_comm
-- name    : TunnellMap.vadd_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:23:59.389332+00:00
-- url     : https://prove2.me/theorems/40c6bc8a-b761-550b-b46f-50dc090c8901
-- title:
--   Tunnell Map: vadd comm
-- statement:
--   The Tunnell Map construction uses the vadd comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L20-L21
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L20-L21

import Definitions.Def_TunnellMap_PrimitiveDirection
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_ProjectiveKey
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.vadd_comm (p q : Triple) : vadd p q = vadd q p := by sorry
