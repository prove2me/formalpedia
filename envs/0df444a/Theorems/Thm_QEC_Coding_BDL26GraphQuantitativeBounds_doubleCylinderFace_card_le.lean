-- Prove2me | Theorems.Thm_QEC_Coding_BDL26GraphQuantitativeBounds_doubleCylinderFace_card_le
-- name    : QEC.Coding.BDL26GraphQuantitativeBounds.doubleCylinderFace_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:58:26.709768+00:00
-- url     : https://prove2.me/theorems/4523e8bf-4d92-45b4-8271-d1a32375606d
-- title:
--   BDL26 Graph Quantitative Bounds: double Cylinder Face card le
-- statement:
--   Degree-two X-local syndrome coordinates obey the same envelope.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GraphQuantitativeBounds.lean#L265-L273
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GraphQuantitativeBounds.lean#L265-L273

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

theorem QEC.Coding.BDL26GraphQuantitativeBounds.doubleCylinderFace_card_le (P : TannerSquarePresentation)
    (h : BoundedValence P) (x : P.X) (S : OddScale) :
    Fintype.card (DoubleCylinderFace P x S) ≤ localCoordinateBound S := by sorry
