-- Prove2me | Theorems.Thm_TunnellMap_dot_tau
-- name    : TunnellMap.dot_tau
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:44:26.937886+00:00
-- url     : https://prove2.me/theorems/24dfb78b-bfbd-5062-ae31-8fca01c08eb5
-- title:
--   Tunnell Map: dot tau
-- statement:
--   The Tunnell Map construction uses the dot tau property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/AffineLattice.lean#L35-L38
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/AffineLattice.lean#L35-L38

import Definitions.Def_TunnellMap_Midpoint
import Definitions.Def_TunnellMap_AffineLattice
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.dot_tau (p q : Triple) : dot (tau p) (tau q) =
    2 * p.x * q.x + p.y * q.y + 2 * p.z * q.z := by sorry
