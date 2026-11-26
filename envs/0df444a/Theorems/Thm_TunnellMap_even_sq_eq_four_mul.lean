-- Prove2me | Theorems.Thm_TunnellMap_even_sq_eq_four_mul
-- name    : TunnellMap.even_sq_eq_four_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:40:26.169628+00:00
-- url     : https://prove2.me/theorems/ec7f2eda-4b1c-5d4c-9735-f67887349295
-- title:
--   Tunnell Map: even sq eq four mul
-- statement:
--   The Tunnell Map construction uses the even sq eq four mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Midpoint.lean#L45-L50
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Midpoint.lean#L45-L50

import Definitions.Def_TunnellMap_QuarterTurns
import Definitions.Def_TunnellMap_Midpoint
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.even_sq_eq_four_mul {x : ℤ} (hx : Even x) :
    ∃ k : ℤ, x ^ 2 = 4 * k := by sorry
