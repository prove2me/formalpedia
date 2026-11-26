-- Prove2me | Theorems.Thm_TunnellMap_Examples41_directionKey_neg_two_vsmul
-- name    : TunnellMap.Examples41.directionKey_neg_two_vsmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:22:50.303073+00:00
-- url     : https://prove2.me/theorems/9c66f2c3-9e0d-5fb7-a037-04de91074b8b
-- title:
--   Examples41: direction Key neg two vsmul
-- statement:
--   The Examples41 construction uses the direction Key neg two vsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Residual.lean#L215-L225
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Residual.lean#L215-L225

import Definitions.Def_TunnellMap_Examples41
import Definitions.Def_TunnellMap_Examples41Residual
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.directionKey_neg_two_vsmul (d : Triple) (hd : d ≠ ⟨0, 0, 0⟩) :
    directionKey (vsmul (-2) d) = directionKey d := by sorry
