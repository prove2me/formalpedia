-- Prove2me | Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_leastOddScaleAbove_minimal
-- name    : QEC.Coding.BDL26QuantitativeBounds.leastOddScaleAbove_minimal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T04:20:42.385574+00:00
-- url     : https://prove2.me/theorems/81c36e72-d223-411f-a5d8-308d58e19067
-- title:
--   BDL26 Quantitative Bounds: least Odd Scale Above minimal
-- statement:
--   Exact minimality among odd integers, including the strict threshold boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L453-L456
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L453-L456

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26QuantitativeBounds
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26DecodingGraph

theorem QEC.Coding.BDL26QuantitativeBounds.leastOddScaleAbove_minimal (threshold : ℝ) (hone : 1 ≤ threshold)
    (n : Nat) (hodd : n % 2 = 1) (hgt : threshold < n) :
    (leastOddScaleAbove threshold hone).ell ≤ n := by sorry
