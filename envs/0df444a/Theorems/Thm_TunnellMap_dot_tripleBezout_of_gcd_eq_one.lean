-- Prove2me | Theorems.Thm_TunnellMap_dot_tripleBezout_of_gcd_eq_one
-- name    : TunnellMap.dot_tripleBezout_of_gcd_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:48:05.101374+00:00
-- url     : https://prove2.me/theorems/5944bbb7-bd18-5309-9563-81388f2b2ad9
-- title:
--   Tunnell Map: dot triple Bezout of gcd eq one
-- statement:
--   The Tunnell Map construction uses the dot triple Bezout of gcd eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrthogonalFrameExistence.lean#L23-L37
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrthogonalFrameExistence.lean#L23-L37

import Definitions.Def_TunnellMap_AffineLattice
import Definitions.Def_TunnellMap_OrthogonalFrameExistence
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.dot_tripleBezout_of_gcd_eq_one {p : Triple} (hp : tripleGCD p = 1) :
    dot p (tripleBezout p) = 1 := by sorry
