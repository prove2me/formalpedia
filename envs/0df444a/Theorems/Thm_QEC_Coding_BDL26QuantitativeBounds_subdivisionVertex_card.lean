-- Prove2me | Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_subdivisionVertex_card
-- name    : QEC.Coding.BDL26QuantitativeBounds.subdivisionVertex_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:43:19.295836+00:00
-- url     : https://prove2.me/theorems/eae8e6e1-4c65-48e1-af10-962c7426a9f8
-- title:
--   BDL26 Quantitative Bounds: subdivision Vertex card
-- statement:
--   Exact subdivision vertex count, including boundary and interior tags.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L18-L24
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L18-L24

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26QuantitativeBounds
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26DecodingGraph

theorem QEC.Coding.BDL26QuantitativeBounds.subdivisionVertex_card (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    Fintype.card (SubdivisionVertex P x S) =
      Fintype.card (XStarVertex P x) +
      Fintype.card (XStarEdge P x) * (S.half - 1) +
      Fintype.card (XStarFace P x) * (S.half - 1) * (S.half - 1) := by sorry
