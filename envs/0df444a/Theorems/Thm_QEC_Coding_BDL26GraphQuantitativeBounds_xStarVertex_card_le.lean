-- Prove2me | Theorems.Thm_QEC_Coding_BDL26GraphQuantitativeBounds_xStarVertex_card_le
-- name    : QEC.Coding.BDL26GraphQuantitativeBounds.xStarVertex_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:58:13.624299+00:00
-- url     : https://prove2.me/theorems/559d6cea-b72c-4b84-a044-25cffe265b50
-- title:
--   BDL26 Graph Quantitative Bounds: x Star Vertex card le
-- statement:
--   A finite bound on all local-star vertices, derived from actual face cover.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GraphQuantitativeBounds.lean#L200-L205
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GraphQuantitativeBounds.lean#L200-L205

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

theorem QEC.Coding.BDL26GraphQuantitativeBounds.xStarVertex_card_le (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (h : BoundedValence P) (x : P.X) : Fintype.card (XStarVertex P x) ≤ 56 := by sorry
