-- Prove2me | Theorems.Thm_TunnellMap_triplePolynomial_negTriple
-- name    : TunnellMap.triplePolynomial_negTriple
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:55:35.320265+00:00
-- url     : https://prove2.me/theorems/9efa1072-28f0-4330-b8f6-967d02f67739
-- title:
--   Tunnell Map: triple Polynomial neg Triple
-- statement:
--   The Tunnell Map construction uses the triple Polynomial neg Triple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L51-L54
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L51-L54

import Definitions.Def_TunnellMap_AffineLattice
import Definitions.Def_TunnellMap_Antipodal
import Definitions.Def_TunnellMap_PrimitiveDirection
set_option autoImplicit true
open TunnellMap
open Polynomial

theorem TunnellMap.triplePolynomial_negTriple (v : Triple) :
    triplePolynomial (negTriple v) = -triplePolynomial v := by sorry
