-- Prove2me | Theorems.Thm_TunnellMap_dot_cross_self_right
-- name    : TunnellMap.dot_cross_self_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:45:21.471851+00:00
-- url     : https://prove2.me/theorems/899aa49f-ac99-4471-aa8a-fa7bc2e4eb59
-- title:
--   Tunnell Map: dot cross self right
-- statement:
--   The Tunnell Map construction uses the dot cross self right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/AffineLattice.lean#L48-L50
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/AffineLattice.lean#L48-L50

import Definitions.Def_TunnellMap_Midpoint
import Definitions.Def_TunnellMap_AffineLattice
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.dot_cross_self_right (p q : Triple) : dot q (cross p q) = 0 := by sorry
