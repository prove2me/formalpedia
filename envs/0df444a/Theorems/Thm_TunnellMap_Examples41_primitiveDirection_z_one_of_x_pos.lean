-- Prove2me | Theorems.Thm_TunnellMap_Examples41_primitiveDirection_z_one_of_x_pos
-- name    : TunnellMap.Examples41.primitiveDirection_z_one_of_x_pos
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:24:47.648544+00:00
-- url     : https://prove2.me/theorems/17407e1f-2df3-407c-8865-f60d0814e95e
-- title:
--   Examples41: primitive Direction z one of x pos
-- statement:
--   The Examples41 construction uses the primitive Direction z one of x pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Residual.lean#L199-L203
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Residual.lean#L199-L203

import Definitions.Def_TunnellMap_Examples41
import Definitions.Def_TunnellMap_Examples41Residual
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.primitiveDirection_z_one_of_x_pos (x y : ℤ) (hx : 0 < x) :
    primitiveDirection ⟨x, y, 1⟩ = ⟨x, y, 1⟩ := by sorry
