-- Prove2me | Theorems.Thm_TunnellMap_lagrange_identity
-- name    : TunnellMap.lagrange_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:45:09.068131+00:00
-- url     : https://prove2.me/theorems/34f1d69b-d296-477a-8319-f3b30d472c71
-- title:
--   Tunnell Map: lagrange identity
-- statement:
--   The Tunnell Map construction uses the lagrange identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/AffineLattice.lean#L52-L55
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/AffineLattice.lean#L52-L55

import Definitions.Def_TunnellMap_Midpoint
import Definitions.Def_TunnellMap_AffineLattice
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.lagrange_identity (p q : Triple) :
    dot (cross p q) (cross p q) = dot p p * dot q q - dot p q ^ 2 := by sorry
