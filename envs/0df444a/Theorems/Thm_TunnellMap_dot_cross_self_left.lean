-- Prove2me | Theorems.Thm_TunnellMap_dot_cross_self_left
-- name    : TunnellMap.dot_cross_self_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:45:16.103038+00:00
-- url     : https://prove2.me/theorems/841c2b48-ba89-4a48-99d6-9307bb1bf050
-- title:
--   Tunnell Map: dot cross self left
-- statement:
--   The Tunnell Map construction uses the dot cross self left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/AffineLattice.lean#L44-L46
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/AffineLattice.lean#L44-L46

import Definitions.Def_TunnellMap_Midpoint
import Definitions.Def_TunnellMap_AffineLattice
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.dot_cross_self_left (p q : Triple) : dot p (cross p q) = 0 := by sorry
