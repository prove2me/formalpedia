-- Prove2me | Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_qDoubleCylinderEdge_card
-- name    : QEC.Coding.BDL26QuantitativeBounds.qDoubleCylinderEdge_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:36:46.179562+00:00
-- url     : https://prove2.me/theorems/cca1e0c8-73c8-4df1-9221-07736d53655c
-- title:
--   BDL26 Quantitative Bounds: q Double Cylinder Edge card
-- statement:
--   Exact Q-local syndrome-coordinate count: two end paths and vertical edges.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L72-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L72-L79

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26QuantitativeBounds
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26DecodingGraph

theorem QEC.Coding.BDL26QuantitativeBounds.qDoubleCylinderEdge_card (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) :
    Fintype.card (QDoubleCylinderEdge P q S) =
      Fintype.card (QStarEdge P q) * S.ell := by sorry
