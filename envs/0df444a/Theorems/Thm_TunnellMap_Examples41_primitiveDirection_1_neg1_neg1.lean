-- Prove2me | Theorems.Thm_TunnellMap_Examples41_primitiveDirection_1_neg1_neg1
-- name    : TunnellMap.Examples41.primitiveDirection_1_neg1_neg1
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:26:32.764541+00:00
-- url     : https://prove2.me/theorems/fd69f1a4-cfd7-50cc-9bc2-668a5c3230a3
-- title:
--   Examples41: primitive Direction 1 neg1 neg1
-- statement:
--   The Examples41 construction uses the primitive Direction 1 neg1 neg1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Residual.lean#L227-L231
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Residual.lean#L227-L231

import Definitions.Def_TunnellMap_Examples41
import Definitions.Def_TunnellMap_Examples41Residual
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.primitiveDirection_1_neg1_neg1 :
    primitiveDirection ⟨1, -1, -1⟩ = ⟨1, -1, -1⟩ := by sorry
