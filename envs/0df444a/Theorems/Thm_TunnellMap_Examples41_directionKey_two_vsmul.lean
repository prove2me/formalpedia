-- Prove2me | Theorems.Thm_TunnellMap_Examples41_directionKey_two_vsmul
-- name    : TunnellMap.Examples41.directionKey_two_vsmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:24:56.807001+00:00
-- url     : https://prove2.me/theorems/1fdec705-8ea2-4660-8927-6ead4d86e41e
-- title:
--   Examples41: direction Key two vsmul
-- statement:
--   The Examples41 construction uses the direction Key two vsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Residual.lean#L211-L213
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Residual.lean#L211-L213

import Definitions.Def_TunnellMap_Examples41
import Definitions.Def_TunnellMap_Examples41Residual
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.directionKey_two_vsmul (d : Triple) (hd : d ≠ ⟨0, 0, 0⟩) :
    directionKey (vsmul 2 d) = directionKey d := by sorry
