-- Prove2me | Theorems.Thm_TunnellMap_representativeEdgeKey_neg_source
-- name    : TunnellMap.representativeEdgeKey_neg_source
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:21:23.801924+00:00
-- url     : https://prove2.me/theorems/6ec0ac17-78cb-5e94-8bd0-3fdeb1023818
-- title:
--   Tunnell Map: representative Edge Key neg source
-- statement:
--   The Tunnell Map construction uses the representative Edge Key neg source property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L278-L283
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L278-L283

import Definitions.Def_TunnellMap_PrimitiveDirection
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_ProjectiveKey
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.representativeEdgeKey_neg_source {n : ℤ}
    (s : BResidual n) (t : AResidual n) :
    representativeEdgeKey (negBResidual s) t = representativeEdgeKey s t := by sorry
