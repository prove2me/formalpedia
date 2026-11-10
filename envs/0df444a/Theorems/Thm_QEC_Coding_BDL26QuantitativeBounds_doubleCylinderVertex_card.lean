-- Prove2me | Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_doubleCylinderVertex_card
-- name    : QEC.Coding.BDL26QuantitativeBounds.doubleCylinderVertex_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:43:39.956987+00:00
-- url     : https://prove2.me/theorems/25db3d84-e6dc-4d6a-9023-e72b480649e4
-- title:
--   BDL26 Quantitative Bounds: double Cylinder Vertex card
-- statement:
--   The intrinsic local zero-cells consist of two disjoint copies.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L42-L49
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L42-L49

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26QuantitativeBounds
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26DecodingGraph

theorem QEC.Coding.BDL26QuantitativeBounds.doubleCylinderVertex_card (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) :
    Fintype.card (DoubleCylinderVertex P x S) =
      2 * (Fintype.card (XStarVertex P x) +
        Fintype.card (XStarEdge P x) * (S.half - 1) +
        Fintype.card (XStarFace P x) * (S.half - 1) * (S.half - 1)) := by sorry
