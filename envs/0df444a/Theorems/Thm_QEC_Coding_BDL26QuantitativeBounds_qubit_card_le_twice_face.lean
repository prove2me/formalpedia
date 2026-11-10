-- Prove2me | Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_qubit_card_le_twice_face
-- name    : QEC.Coding.BDL26QuantitativeBounds.qubit_card_le_twice_face
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:44:50.266532+00:00
-- url     : https://prove2.me/theorems/4b4407de-e1d4-45d2-a988-e803f117a8c6
-- title:
--   BDL26 Quantitative Bounds: qubit card le twice face
-- statement:
--   Every actual qubit is covered by one of two corners of a face.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L167-L171
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L167-L171

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26QuantitativeBounds
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26DecodingGraph

theorem QEC.Coding.BDL26QuantitativeBounds.qubit_card_le_twice_face (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) :
    Fintype.card P.Q ≤ 2 * Fintype.card P.Face := by sorry
