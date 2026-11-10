-- Prove2me | Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_qDoubleCylinderVertex_card
-- name    : QEC.Coding.BDL26QuantitativeBounds.qDoubleCylinderVertex_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:44:17.331264+00:00
-- url     : https://prove2.me/theorems/788e872d-30e3-456c-85fa-b2e272df50bd
-- title:
--   BDL26 Quantitative Bounds: q Double Cylinder Vertex card
-- statement:
--   Exact Q-local intrinsic zero-cell count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L64-L69
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L64-L69

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26QuantitativeBounds
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26DecodingGraph

theorem QEC.Coding.BDL26QuantitativeBounds.qDoubleCylinderVertex_card (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) :
    Fintype.card (QDoubleCylinderVertex P q S) =
      2 * (1 + Fintype.card (QStarEdge P q) * S.half) := by sorry
