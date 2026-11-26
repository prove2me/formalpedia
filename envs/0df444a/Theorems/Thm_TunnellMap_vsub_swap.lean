-- Prove2me | Theorems.Thm_TunnellMap_vsub_swap
-- name    : TunnellMap.vsub_swap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:24:03.810672+00:00
-- url     : https://prove2.me/theorems/68d915f0-6880-58ab-9044-18c1d5d41cf0
-- title:
--   Tunnell Map: vsub swap
-- statement:
--   The Tunnell Map construction uses the vsub swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L23-L24
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L23-L24

import Definitions.Def_TunnellMap_PrimitiveDirection
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_ProjectiveKey
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.vsub_swap (p q : Triple) : vsub p q = negTriple (vsub q p) := by sorry
