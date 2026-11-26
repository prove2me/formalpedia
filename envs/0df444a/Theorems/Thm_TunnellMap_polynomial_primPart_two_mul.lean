-- Prove2me | Theorems.Thm_TunnellMap_polynomial_primPart_two_mul
-- name    : TunnellMap.polynomial_primPart_two_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:56:48.576276+00:00
-- url     : https://prove2.me/theorems/c93405e9-c3bb-4a8e-b685-a67d77d31e24
-- title:
--   Tunnell Map: polynomial prim Part two mul
-- statement:
--   The Tunnell Map construction uses the polynomial prim Part two mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L132-L149
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L132-L149

import Definitions.Def_TunnellMap_AffineLattice
import Definitions.Def_TunnellMap_Antipodal
import Definitions.Def_TunnellMap_PrimitiveDirection
set_option autoImplicit true
open TunnellMap
open Polynomial

theorem TunnellMap.polynomial_primPart_two_mul {f : ℤ[X]} (hf : f ≠ 0) :
    (C (2 : ℤ) * f).primPart = f.primPart := by sorry
