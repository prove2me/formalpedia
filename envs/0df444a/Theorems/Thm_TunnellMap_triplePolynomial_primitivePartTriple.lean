-- Prove2me | Theorems.Thm_TunnellMap_triplePolynomial_primitivePartTriple
-- name    : TunnellMap.triplePolynomial_primitivePartTriple
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:56:36.509382+00:00
-- url     : https://prove2.me/theorems/61e1f238-8108-5399-ae7a-ef2fa823ca9d
-- title:
--   Tunnell Map: triple Polynomial primitive Part Triple
-- statement:
--   Converting the primitive polynomial back to a triple loses no
--   coefficients, because the original polynomial has degree at most two.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L92-L107
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L92-L107

import Definitions.Def_TunnellMap_AffineLattice
import Definitions.Def_TunnellMap_Antipodal
import Definitions.Def_TunnellMap_PrimitiveDirection
set_option autoImplicit true
open TunnellMap
open Polynomial

theorem TunnellMap.triplePolynomial_primitivePartTriple (v : Triple) :
    triplePolynomial (primitivePartTriple v) = (triplePolynomial v).primPart := by sorry
