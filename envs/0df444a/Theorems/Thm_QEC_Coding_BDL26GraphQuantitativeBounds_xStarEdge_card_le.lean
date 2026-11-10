-- Prove2me | Theorems.Thm_QEC_Coding_BDL26GraphQuantitativeBounds_xStarEdge_card_le
-- name    : QEC.Coding.BDL26GraphQuantitativeBounds.xStarEdge_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:39:33.159195+00:00
-- url     : https://prove2.me/theorems/22c72829-1613-40d5-af31-0a66e473e046
-- title:
--   BDL26 Graph Quantitative Bounds: x Star Edge card le
-- statement:
--   The BDL26 Graph Quantitative Bounds construction uses the x Star Edge card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GraphQuantitativeBounds.lean#L231-L236
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GraphQuantitativeBounds.lean#L231-L236

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

theorem QEC.Coding.BDL26GraphQuantitativeBounds.xStarEdge_card_le (P : TannerSquarePresentation) (h : BoundedValence P) (x : P.X) :
    Fintype.card (XStarEdge P x) ≤ 56 := by sorry
