-- Prove2me | Theorems.Thm_TunnellMap_triplePolynomial_coeff_one
-- name    : TunnellMap.triplePolynomial_coeff_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:54:59.407192+00:00
-- url     : https://prove2.me/theorems/e4acbcc7-ab71-4d6f-8e3f-673037f10abc
-- title:
--   Tunnell Map: triple Polynomial coeff one
-- statement:
--   The Tunnell Map construction uses the triple Polynomial coeff one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L31-L35
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L31-L35

import Definitions.Def_TunnellMap_AffineLattice
import Definitions.Def_TunnellMap_Antipodal
import Definitions.Def_TunnellMap_PrimitiveDirection
set_option autoImplicit true
open TunnellMap
open Polynomial

theorem TunnellMap.triplePolynomial_coeff_one (v : Triple) :
    (triplePolynomial v).coeff 1 = v.y := by sorry
