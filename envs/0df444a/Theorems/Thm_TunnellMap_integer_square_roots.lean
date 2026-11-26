-- Prove2me | Theorems.Thm_TunnellMap_integer_square_roots
-- name    : TunnellMap.integer_square_roots
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:52:53.1411+00:00
-- url     : https://prove2.me/theorems/9c22bfd5-225b-4b19-bd72-de6825b127a8
-- title:
--   Tunnell Map: integer square roots
-- statement:
--   The Tunnell Map construction uses the integer square roots property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/QuadraticRoots.lean#L41-L43
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/QuadraticRoots.lean#L41-L43

import Definitions.Def_TunnellMap_ShortInterval
import Definitions.Def_TunnellMap_QuadraticRoots
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.integer_square_roots {u s : ℤ} (h : u ^ 2 = s ^ 2) :
    u = s ∨ u = -s := by sorry
