-- Prove2me | Theorems.Thm_TunnellMap_Examples41_directionKey_two_1_neg1_neg1
-- name    : TunnellMap.Examples41.directionKey_two_1_neg1_neg1
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T17:06:18.326563+00:00
-- url     : https://prove2.me/theorems/a81a76e1-0e88-41bc-9a32-1180a7321b37
-- title:
--   Examples41: direction Key two 1 neg1 neg1
-- statement:
--   The Examples41 construction uses the direction Key two 1 neg1 neg1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Residual.lean#L233-L237
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Residual.lean#L233-L237

import Definitions.Def_TunnellMap_Examples41
import Definitions.Def_TunnellMap_Examples41Residual
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.directionKey_two_1_neg1_neg1 :
    directionKey (vsmul 2 ⟨1, -1, -1⟩) = (⟨5, 1, -1, -1⟩ : DirectionKey) := by sorry
