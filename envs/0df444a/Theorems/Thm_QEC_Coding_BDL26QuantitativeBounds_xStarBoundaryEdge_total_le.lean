-- Prove2me | Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_xStarBoundaryEdge_total_le
-- name    : QEC.Coding.BDL26QuantitativeBounds.xStarBoundaryEdge_total_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:45:41.602355+00:00
-- url     : https://prove2.me/theorems/c39ca55a-67e1-4237-868b-3f0c7cad22dc
-- title:
--   BDL26 Quantitative Bounds: x Star Boundary Edge total le
-- statement:
--   Boundary edge count uses actual face sides, not an assumed local-size bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L258-L262
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L258-L262

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26QuantitativeBounds
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26DecodingGraph

theorem QEC.Coding.BDL26QuantitativeBounds.xStarBoundaryEdge_total_le (P : TannerSquarePresentation) :
    (∑ x : P.X, Fintype.card (XStarBoundaryEdge P x)) ≤ 2 * Fintype.card P.Face := by sorry
