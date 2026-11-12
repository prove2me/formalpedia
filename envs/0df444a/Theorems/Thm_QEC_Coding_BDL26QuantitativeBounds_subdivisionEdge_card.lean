-- Prove2me | Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_subdivisionEdge_card
-- name    : QEC.Coding.BDL26QuantitativeBounds.subdivisionEdge_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T04:18:11.907583+00:00
-- url     : https://prove2.me/theorems/cb85a467-5621-4081-9d16-8048b4b2f967
-- title:
--   BDL26 Quantitative Bounds: subdivision Edge card
-- statement:
--   Exact count of subdivided old edges and both square-interior directions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L27-L32
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L27-L32

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26QuantitativeBounds
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26DecodingGraph

theorem QEC.Coding.BDL26QuantitativeBounds.subdivisionEdge_card (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    Fintype.card (SubdivisionEdge P x S) =
      Fintype.card (XStarEdge P x) * S.half +
      2 * Fintype.card (XStarFace P x) * S.half * (S.half - 1) := by sorry
