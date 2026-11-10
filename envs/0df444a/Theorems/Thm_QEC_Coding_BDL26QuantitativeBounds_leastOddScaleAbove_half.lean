-- Prove2me | Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_leastOddScaleAbove_half
-- name    : QEC.Coding.BDL26QuantitativeBounds.leastOddScaleAbove_half
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T04:20:13.008594+00:00
-- url     : https://prove2.me/theorems/71d694df-294f-4508-be9b-74f09ccdaa77
-- title:
--   BDL26 Quantitative Bounds: least Odd Scale Above half
-- statement:
--   The canonical half-scale remains exactly the source's subdivision parameter.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L459-L464
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L459-L464

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26QuantitativeBounds
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26DecodingGraph

theorem QEC.Coding.BDL26QuantitativeBounds.leastOddScaleAbove_half (threshold : ℝ) (hone : 1 ≤ threshold) :
    (leastOddScaleAbove threshold hone).half = (⌊threshold⌋₊ + 1) / 2 := by sorry
