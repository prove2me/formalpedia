-- Prove2me | Theorems.Thm_QEC_Coding_BDL26GraphQuantitativeBounds_rxSyndromeCell_card_le
-- name    : QEC.Coding.BDL26GraphQuantitativeBounds.rxSyndromeCell_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:16:24.174666+00:00
-- url     : https://prove2.me/theorems/b3352d9f-5cf8-4506-9938-4abcc00b70c8
-- title:
--   BDL26 Graph Quantitative Bounds: rx Syndrome Cell card le
-- statement:
--   The cardinality counts syndrome coordinates rather than the union of all cells.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GraphQuantitativeBounds.lean#L587-L598
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GraphQuantitativeBounds.lean#L587-L598

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26GraphQuantitativeBounds
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26QuantitativeBounds BDL26BoundedValence
open BDL26FiniteAlternatingCore BDL26RXLocalReplacement
open scoped BigOperators Classical
open BDL26ReplacementSupport

theorem QEC.Coding.BDL26GraphQuantitativeBounds.rxSyndromeCell_card_le (P : TannerSquarePresentation) (h : BoundedValence P)
    (S : OddScale) (u : Vertex P) :
    Fintype.card (RXSyndromeCell P S u) ≤ localCoordinateBound S := by sorry
