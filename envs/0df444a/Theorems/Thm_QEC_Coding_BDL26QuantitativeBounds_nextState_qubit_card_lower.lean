-- Prove2me | Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_nextState_qubit_card_lower
-- name    : QEC.Coding.BDL26QuantitativeBounds.nextState_qubit_card_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:22:23.406042+00:00
-- url     : https://prove2.me/theorems/0ed57674-5de3-4228-9e7b-51bd0c1fdad2
-- title:
--   BDL26 Quantitative Bounds: next State qubit card lower
-- statement:
--   The lower recurrence follows from the selected RX/RZ constructors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L130-L141
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L130-L141

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26QuantitativeBounds
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26DecodingGraph

theorem QEC.Coding.BDL26QuantitativeBounds.nextState_qubit_card_lower (S : OddScale) (n : Nat) (C : ConstructionState) :
    2 * Fintype.card C.presentation.Q ≤
      Fintype.card (nextState S n C).presentation.Q := by sorry
