-- Prove2me | Theorems.Thm_TunnellMap_Examples41_primitiveDirection_z_neg_one_of_x_pos
-- name    : TunnellMap.Examples41.primitiveDirection_z_neg_one_of_x_pos
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:23:32.130654+00:00
-- url     : https://prove2.me/theorems/e76246f4-5179-5bfe-ada3-038ae625fb42
-- title:
--   Examples41: primitive Direction z neg one of x pos
-- statement:
--   The Examples41 construction uses the primitive Direction z neg one of x pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Residual.lean#L205-L209
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Residual.lean#L205-L209

import Definitions.Def_TunnellMap_Examples41
import Definitions.Def_TunnellMap_Examples41Residual
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.primitiveDirection_z_neg_one_of_x_pos (x y : ℤ) (hx : 0 < x) :
    primitiveDirection ⟨x, y, -1⟩ = ⟨x, y, -1⟩ := by sorry
