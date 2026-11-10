-- Prove2me | Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_doubleCylinderFace_card
-- name    : QEC.Coding.BDL26QuantitativeBounds.doubleCylinderFace_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:28:35.081566+00:00
-- url     : https://prove2.me/theorems/fe36491b-f65e-4f17-a5c4-89ff8d273d45
-- title:
--   BDL26 Quantitative Bounds: double Cylinder Face card
-- statement:
--   The BDL26 Quantitative Bounds construction uses the double Cylinder Face card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L288-L295
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L288-L295

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26QuantitativeBounds
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26DecodingGraph

theorem QEC.Coding.BDL26QuantitativeBounds.doubleCylinderFace_card (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) :
    Fintype.card (DoubleCylinderFace P x S) =
      2 * Fintype.card (XStarFace P x) * S.half ^ 2 +
      Fintype.card (XStarBoundaryEdge P x) * S.half := by sorry
