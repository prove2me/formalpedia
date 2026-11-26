-- Prove2me | Theorems.Thm_TunnellMap_triplePolynomial_coeff_zero
-- name    : TunnellMap.triplePolynomial_coeff_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:54:57.245798+00:00
-- url     : https://prove2.me/theorems/01726c21-4c2a-45e6-9c2b-a6bca7f95d39
-- title:
--   Tunnell Map: triple Polynomial coeff zero
-- statement:
--   The Tunnell Map construction uses the triple Polynomial coeff zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L27-L29
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L27-L29

import Definitions.Def_TunnellMap_AffineLattice
import Definitions.Def_TunnellMap_Antipodal
import Definitions.Def_TunnellMap_PrimitiveDirection
set_option autoImplicit true
open TunnellMap
open Polynomial

theorem TunnellMap.triplePolynomial_coeff_zero (v : Triple) :
    (triplePolynomial v).coeff 0 = v.x := by sorry
