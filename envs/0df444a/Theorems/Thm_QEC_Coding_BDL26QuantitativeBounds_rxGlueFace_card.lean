-- Prove2me | Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_rxGlueFace_card
-- name    : QEC.Coding.BDL26QuantitativeBounds.rxGlueFace_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:37:21.845592+00:00
-- url     : https://prove2.me/theorems/a5bba3a6-434c-4dcc-b8eb-eadba48a05d3
-- title:
--   BDL26 Quantitative Bounds: rx Glue Face card
-- statement:
--   The glue-face count is linear in actual old face count by perfect pairing.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L306-L316
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L306-L316

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26QuantitativeBounds
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26DecodingGraph

theorem QEC.Coding.BDL26QuantitativeBounds.rxGlueFace_card (P : TannerSquarePresentation) (S : OddScale) :
    Fintype.card (RXXQGlueFace P S) = 4 * S.ell * Fintype.card P.Face := by sorry
