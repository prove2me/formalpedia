-- Prove2me | Theorems.Thm_TunnellMap_polynomialTriple_neg
-- name    : TunnellMap.polynomialTriple_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:54:36.495182+00:00
-- url     : https://prove2.me/theorems/4c45ffd0-4aa4-54bf-b1d5-29bf46c2621b
-- title:
--   Tunnell Map: polynomial Triple neg
-- statement:
--   The Tunnell Map construction uses the polynomial Triple neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L23-L25
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L23-L25

import Definitions.Def_TunnellMap_AffineLattice
import Definitions.Def_TunnellMap_Antipodal
import Definitions.Def_TunnellMap_PrimitiveDirection
set_option autoImplicit true
open TunnellMap
open Polynomial

theorem TunnellMap.polynomialTriple_neg (f : ℤ[X]) :
    polynomialTriple (-f) = negTriple (polynomialTriple f) := by sorry
