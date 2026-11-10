-- Prove2me | Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_state_qubit_card_upper
-- name    : QEC.Coding.BDL26QuantitativeBounds.state_qubit_card_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:30:39.666203+00:00
-- url     : https://prove2.me/theorems/6ab2e616-663a-4c06-aa7a-94cab0126a5a
-- title:
--   BDL26 Quantitative Bounds: state qubit card upper
-- statement:
--   Explicit finite upper bound, with no asymptotic or degree-bound premise.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L405-L412
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L405-L412

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26QuantitativeBounds
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26DecodingGraph

theorem QEC.Coding.BDL26QuantitativeBounds.state_qubit_card_upper (S : OddScale) (n : Nat) :
    Fintype.card (state S n).presentation.Q ≤ 8 * faceGrowthFactor S ^ n := by sorry
