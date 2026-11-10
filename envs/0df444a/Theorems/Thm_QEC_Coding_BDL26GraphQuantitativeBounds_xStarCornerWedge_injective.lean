-- Prove2me | Theorems.Thm_QEC_Coding_BDL26GraphQuantitativeBounds_xStarCornerWedge_injective
-- name    : QEC.Coding.BDL26GraphQuantitativeBounds.xStarCornerWedge_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:57:35.334222+00:00
-- url     : https://prove2.me/theorems/234af328-10fc-43b2-93eb-702fb29480e7
-- title:
--   BDL26 Graph Quantitative Bounds: x Star Corner Wedge injective
-- statement:
--   The BDL26 Graph Quantitative Bounds construction uses the x Star Corner Wedge injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GraphQuantitativeBounds.lean#L123-L139
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GraphQuantitativeBounds.lean#L123-L139

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

theorem QEC.Coding.BDL26GraphQuantitativeBounds.xStarCornerWedge_injective (P : TannerSquarePresentation) (x : P.X) :
    Function.Injective (xStarCornerWedge P x) := by sorry
