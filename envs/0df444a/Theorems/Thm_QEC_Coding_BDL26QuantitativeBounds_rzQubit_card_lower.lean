-- Prove2me | Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_rzQubit_card_lower
-- name    : QEC.Coding.BDL26QuantitativeBounds.rzQubit_card_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:44:26.164455+00:00
-- url     : https://prove2.me/theorems/aab243a0-3b67-47a1-a002-de20c1c46a9f
-- title:
--   BDL26 Quantitative Bounds: rz Qubit card lower
-- statement:
--   Actual RZ replacement at least doubles the qubit count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L124-L127
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L124-L127

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26QuantitativeBounds
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26DecodingGraph

theorem QEC.Coding.BDL26QuantitativeBounds.rzQubit_card_lower (P : TannerSquarePresentation) (S : OddScale) :
    2 * Fintype.card P.Q ≤ Fintype.card (BDL26RZLocalReplacement.RZQ P S) := by sorry
