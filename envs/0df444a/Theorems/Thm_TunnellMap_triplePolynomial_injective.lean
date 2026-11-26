-- Prove2me | Theorems.Thm_TunnellMap_triplePolynomial_injective
-- name    : TunnellMap.triplePolynomial_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:57:22.720613+00:00
-- url     : https://prove2.me/theorems/5591ef5d-fee5-433d-ad1f-071fa3e382bb
-- title:
--   Tunnell Map: triple Polynomial injective
-- statement:
--   The Tunnell Map construction uses the triple Polynomial injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L47-L49
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L47-L49

import Definitions.Def_TunnellMap_AffineLattice
import Definitions.Def_TunnellMap_Antipodal
import Definitions.Def_TunnellMap_PrimitiveDirection
set_option autoImplicit true
open TunnellMap
open Polynomial

theorem TunnellMap.triplePolynomial_injective : Function.Injective triplePolynomial := by sorry
