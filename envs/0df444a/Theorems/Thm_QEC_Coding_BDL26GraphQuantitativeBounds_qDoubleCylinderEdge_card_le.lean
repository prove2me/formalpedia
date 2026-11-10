-- Prove2me | Theorems.Thm_QEC_Coding_BDL26GraphQuantitativeBounds_qDoubleCylinderEdge_card_le
-- name    : QEC.Coding.BDL26GraphQuantitativeBounds.qDoubleCylinderEdge_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:58:27.176416+00:00
-- url     : https://prove2.me/theorems/49032276-4087-4b31-a0de-2c8bfc4b5d49
-- title:
--   BDL26 Graph Quantitative Bounds: q Double Cylinder Edge card le
-- statement:
--   The BDL26 Graph Quantitative Bounds construction uses the q Double Cylinder Edge card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GraphQuantitativeBounds.lean#L285-L293
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GraphQuantitativeBounds.lean#L285-L293

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

theorem QEC.Coding.BDL26GraphQuantitativeBounds.qDoubleCylinderEdge_card_le (P : TannerSquarePresentation)
    (h : BoundedValence P) (q : P.Q) (S : OddScale) :
    Fintype.card (QDoubleCylinderEdge P q S) ≤ localCoordinateBound S := by sorry
