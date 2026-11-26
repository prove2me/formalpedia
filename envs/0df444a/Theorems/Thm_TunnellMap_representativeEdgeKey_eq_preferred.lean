-- Prove2me | Theorems.Thm_TunnellMap_representativeEdgeKey_eq_preferred
-- name    : TunnellMap.representativeEdgeKey_eq_preferred
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:23:09.394419+00:00
-- url     : https://prove2.me/theorems/44ecb2a0-a059-53af-ab56-5e4c7ab6921a
-- title:
--   Tunnell Map: representative Edge Key eq preferred
-- statement:
--   The Tunnell Map construction uses the representative Edge Key eq preferred property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L250-L256
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L250-L256

import Definitions.Def_TunnellMap_PrimitiveDirection
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_ProjectiveKey
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.representativeEdgeKey_eq_preferred {n : ℤ} (s : BResidual n) (t : AResidual n) :
    representativeEdgeKey s t = directionKey (preferredVector s t) := by sorry
