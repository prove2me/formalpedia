-- Prove2me | Theorems.Thm_QEC_Coding_BDL26GraphQuantitativeBounds_doubleCylinderVertex_card_le
-- name    : QEC.Coding.BDL26GraphQuantitativeBounds.doubleCylinderVertex_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:35:06.188101+00:00
-- url     : https://prove2.me/theorems/59a1f220-70c8-42a2-bc5c-1bfc954255b8
-- title:
--   BDL26 Graph Quantitative Bounds: double Cylinder Vertex card le
-- statement:
--   Intrinsic local zero-cells fit the explicit quadratic envelope.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GraphQuantitativeBounds.lean#L252-L262
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GraphQuantitativeBounds.lean#L252-L262

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

theorem QEC.Coding.BDL26GraphQuantitativeBounds.doubleCylinderVertex_card_le (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (h : BoundedValence P) (x : P.X) (S : OddScale) :
    Fintype.card (DoubleCylinderVertex P x S) ≤ localCoordinateBound S := by sorry
