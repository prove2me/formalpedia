-- Prove2me | Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_state_qubit_card_lower
-- name    : QEC.Coding.BDL26QuantitativeBounds.state_qubit_card_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:22:11.590969+00:00
-- url     : https://prove2.me/theorems/a4b86ead-4a73-4e4a-bf6c-e67740ab9045
-- title:
--   BDL26 Quantitative Bounds: state qubit card lower
-- statement:
--   A finite exponential lower bound with the actual five-qubit seed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L144-L154
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L144-L154

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26QuantitativeBounds
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26DecodingGraph

theorem QEC.Coding.BDL26QuantitativeBounds.state_qubit_card_lower (S : OddScale) (n : Nat) :
    5 * 2 ^ n ≤ Fintype.card (state S n).presentation.Q := by sorry
