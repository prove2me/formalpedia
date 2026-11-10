-- Prove2me | Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_leastOddScaleAbove_gt
-- name    : QEC.Coding.BDL26QuantitativeBounds.leastOddScaleAbove_gt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:45:43.579056+00:00
-- url     : https://prove2.me/theorems/363f5bbd-ed66-43ea-9ec6-98cbd87d8b3d
-- title:
--   BDL26 Quantitative Bounds: least Odd Scale Above gt
-- statement:
--   The BDL26 Quantitative Bounds construction uses the least Odd Scale Above gt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L448-L450
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L448-L450

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26QuantitativeBounds
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26DecodingGraph

theorem QEC.Coding.BDL26QuantitativeBounds.leastOddScaleAbove_gt (threshold : ℝ) (hone : 1 ≤ threshold) :
    threshold < (leastOddScaleAbove threshold hone).ell := by sorry
