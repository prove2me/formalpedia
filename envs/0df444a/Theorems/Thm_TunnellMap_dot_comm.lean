-- Prove2me | Theorems.Thm_TunnellMap_dot_comm
-- name    : TunnellMap.dot_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:44:41.709804+00:00
-- url     : https://prove2.me/theorems/34f7ec2a-2dd7-55b1-b9cd-b6c3d6d6400b
-- title:
--   Tunnell Map: dot comm
-- statement:
--   The Tunnell Map construction uses the dot comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/AffineLattice.lean#L31-L33
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/AffineLattice.lean#L31-L33

import Definitions.Def_TunnellMap_Midpoint
import Definitions.Def_TunnellMap_AffineLattice
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.dot_comm (p q : Triple) : dot p q = dot q p := by sorry
