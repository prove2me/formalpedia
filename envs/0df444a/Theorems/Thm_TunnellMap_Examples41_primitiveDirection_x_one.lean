-- Prove2me | Theorems.Thm_TunnellMap_Examples41_primitiveDirection_x_one
-- name    : TunnellMap.Examples41.primitiveDirection_x_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:23:16.886036+00:00
-- url     : https://prove2.me/theorems/2742bb5d-fcdd-4b81-99be-d464a7f5a2c1
-- title:
--   Examples41: primitive Direction x one
-- statement:
--   The Examples41 construction uses the primitive Direction x one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Residual.lean#L193-L197
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Residual.lean#L193-L197

import Definitions.Def_TunnellMap_Examples41
import Definitions.Def_TunnellMap_Examples41Residual
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.primitiveDirection_x_one (y z : ℤ) :
    primitiveDirection ⟨1, y, z⟩ = ⟨1, y, z⟩ := by sorry
