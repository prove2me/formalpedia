-- Prove2me | Theorems.Thm_QEC_Coding_BDL26GraphQuantitativeBounds_rzZeroCell_card_le
-- name    : QEC.Coding.BDL26GraphQuantitativeBounds.rzZeroCell_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:59:54.449811+00:00
-- url     : https://prove2.me/theorems/e33e6a5f-3898-4e84-b335-71a71a0ee939
-- title:
--   BDL26 Graph Quantitative Bounds: rz Zero Cell card le
-- statement:
--   Materialized RZ zero-cells satisfy the same quadratic envelope.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GraphQuantitativeBounds.lean#L351-L365
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GraphQuantitativeBounds.lean#L351-L365

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

theorem QEC.Coding.BDL26GraphQuantitativeBounds.rzZeroCell_card_le (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (h : BoundedValence P) (S : OddScale) (u : Vertex P) :
    Fintype.card (RZZeroCell P S u) ≤ localCoordinateBound S := by sorry
