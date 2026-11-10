-- Prove2me | Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_leastOddAbove_le
-- name    : QEC.Coding.BDL26QuantitativeBounds.leastOddAbove_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:45:45.639795+00:00
-- url     : https://prove2.me/theorems/afda09b1-ab03-4d07-a157-b715b19b861e
-- title:
--   BDL26 Quantitative Bounds: least Odd Above le
-- statement:
--   The BDL26 Quantitative Bounds construction uses the least Odd Above le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L432-L435
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L432-L435

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26QuantitativeBounds
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26DecodingGraph

theorem QEC.Coding.BDL26QuantitativeBounds.leastOddAbove_le (threshold n : Nat) (hodd : n % 2 = 1) (hgt : threshold < n) :
    leastOddAbove threshold ≤ n := by sorry
