-- Prove2me | Theorems.Thm_TunnellMap_polynomialTriple_triplePolynomial
-- name    : TunnellMap.polynomialTriple_triplePolynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:55:17.972565+00:00
-- url     : https://prove2.me/theorems/027b5f3f-c94f-5245-a833-17250175e4ee
-- title:
--   Tunnell Map: polynomial Triple triple Polynomial
-- statement:
--   The Tunnell Map construction uses the polynomial Triple triple Polynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L43-L45
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L43-L45

import Definitions.Def_TunnellMap_AffineLattice
import Definitions.Def_TunnellMap_Antipodal
import Definitions.Def_TunnellMap_PrimitiveDirection
set_option autoImplicit true
open TunnellMap
open Polynomial

theorem TunnellMap.polynomialTriple_triplePolynomial (v : Triple) :
    polynomialTriple (triplePolynomial v) = v := by sorry
