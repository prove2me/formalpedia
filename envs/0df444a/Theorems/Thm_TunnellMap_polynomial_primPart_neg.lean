-- Prove2me | Theorems.Thm_TunnellMap_polynomial_primPart_neg
-- name    : TunnellMap.polynomial_primPart_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:57:05.045711+00:00
-- url     : https://prove2.me/theorems/8637c0e9-aafa-4d4c-a160-e2012e6c2009
-- title:
--   Tunnell Map: polynomial prim Part neg
-- statement:
--   The Tunnell Map construction uses the polynomial prim Part neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L118-L130
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L118-L130

import Definitions.Def_TunnellMap_AffineLattice
import Definitions.Def_TunnellMap_Antipodal
import Definitions.Def_TunnellMap_PrimitiveDirection
set_option autoImplicit true
open TunnellMap
open Polynomial

theorem TunnellMap.polynomial_primPart_neg {f : ℤ[X]} (hf : f ≠ 0) :
    (-f).primPart = -f.primPart := by sorry
