-- Prove2me | Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_rxQubit_card_lower
-- name    : QEC.Coding.BDL26QuantitativeBounds.rxQubit_card_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:44:39.702877+00:00
-- url     : https://prove2.me/theorems/e2fab309-f88d-42c8-88c7-49013a533945
-- title:
--   BDL26 Quantitative Bounds: rx Qubit card lower
-- statement:
--   Actual RX replacement at least doubles the qubit count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L104-L107
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L104-L107

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26QuantitativeBounds
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26DecodingGraph

theorem QEC.Coding.BDL26QuantitativeBounds.rxQubit_card_lower (P : TannerSquarePresentation) (S : OddScale) :
    2 * Fintype.card P.Q ≤ Fintype.card (RX1 P S) := by sorry
