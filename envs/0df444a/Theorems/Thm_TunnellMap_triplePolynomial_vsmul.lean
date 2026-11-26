-- Prove2me | Theorems.Thm_TunnellMap_triplePolynomial_vsmul
-- name    : TunnellMap.triplePolynomial_vsmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:55:54.893226+00:00
-- url     : https://prove2.me/theorems/144f2595-f512-4c10-8a34-10663e1568b1
-- title:
--   Tunnell Map: triple Polynomial vsmul
-- statement:
--   The Tunnell Map construction uses the triple Polynomial vsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L56-L59
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L56-L59

import Definitions.Def_TunnellMap_AffineLattice
import Definitions.Def_TunnellMap_Antipodal
import Definitions.Def_TunnellMap_PrimitiveDirection
set_option autoImplicit true
open TunnellMap
open Polynomial

theorem TunnellMap.triplePolynomial_vsmul (a : ℤ) (v : Triple) :
    triplePolynomial (vsmul a v) = C a * triplePolynomial v := by sorry
