-- Prove2me | Theorems.Thm_TunnellMap_triplePolynomial_ne_zero
-- name    : TunnellMap.triplePolynomial_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:56:23.70416+00:00
-- url     : https://prove2.me/theorems/32eeb163-8ac1-4b57-80ab-07e6fa9c8779
-- title:
--   Tunnell Map: triple Polynomial ne zero
-- statement:
--   The Tunnell Map construction uses the triple Polynomial ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L61-L71
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L61-L71

import Definitions.Def_TunnellMap_AffineLattice
import Definitions.Def_TunnellMap_Antipodal
import Definitions.Def_TunnellMap_PrimitiveDirection
set_option autoImplicit true
open TunnellMap
open Polynomial

theorem TunnellMap.triplePolynomial_ne_zero {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    triplePolynomial v ≠ 0 := by sorry
