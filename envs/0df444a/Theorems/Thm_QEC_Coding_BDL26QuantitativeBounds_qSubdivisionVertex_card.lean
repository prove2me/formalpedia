-- Prove2me | Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_qSubdivisionVertex_card
-- name    : QEC.Coding.BDL26QuantitativeBounds.qSubdivisionVertex_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:44:19.392358+00:00
-- url     : https://prove2.me/theorems/52740a0b-efff-447c-9ab9-ae65650d2854
-- title:
--   BDL26 Quantitative Bounds: q Subdivision Vertex card
-- statement:
--   Q-side path subdivision count, retaining every original endpoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L52-L61
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L52-L61

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26QuantitativeBounds
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26DecodingGraph

theorem QEC.Coding.BDL26QuantitativeBounds.qSubdivisionVertex_card (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) :
    Fintype.card (QSubdivisionVertex P q S) =
      1 + Fintype.card (QStarEdge P q) * S.half := by sorry
