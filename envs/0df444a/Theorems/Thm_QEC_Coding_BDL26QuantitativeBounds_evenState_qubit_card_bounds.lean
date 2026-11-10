-- Prove2me | Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_evenState_qubit_card_bounds
-- name    : QEC.Coding.BDL26QuantitativeBounds.evenState_qubit_card_bounds
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T04:19:47.445428+00:00
-- url     : https://prove2.me/theorems/26e8e8b1-6965-48a5-963d-5ec4d920686d
-- title:
--   BDL26 Quantitative Bounds: even State qubit card bounds
-- statement:
--   Both finite qubit inequalities at the even levels used by the source.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L415-L419
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L415-L419

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26QuantitativeBounds
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26DecodingGraph

theorem QEC.Coding.BDL26QuantitativeBounds.evenState_qubit_card_bounds (S : OddScale) (k : Nat) :
    5 * 2 ^ (2 * k) ≤ Fintype.card (state S (2 * k)).presentation.Q ∧
    Fintype.card (state S (2 * k)).presentation.Q ≤
      8 * (2 * S.ell * (S.ell + 2)) ^ (2 * k) := by sorry
