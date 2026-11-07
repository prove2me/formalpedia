-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_sum_mul_cyclicGeneratorMatrix_pow_shift
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.sum_mul_cyclicGeneratorMatrix_pow_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:02:26.491939+00:00
-- url     : https://prove2.me/theorems/0931208f-3064-482c-9534-fb33ff2231ca
-- title:
--   Cartwright Steger: sum mul cyclic Generator Matrix pow shift
-- statement:
--   Split a shifted full cyclic-basis sum at the wrap point.  The wrapped
--   tail contributes exactly one central factor `1 + y`; no asymptotic or
--   valuation argument is hidden in this reindexing lemma.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L189-L214
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L189-L214

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.sum_mul_cyclicGeneratorMatrix_pow_shift
    (P : BasePrime) (r : Rank) (k : ℕ) (hk : k ≤ r.matrixRank)
    (A : ℕ → Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r)) :
    ∑ i ∈ Finset.range r.matrixRank,
        A i * cyclicGeneratorMatrix P r ^ (k + i) =
      (∑ i ∈ Finset.range (r.matrixRank - k),
        A i * cyclicGeneratorMatrix P r ^ (k + i)) +
      (onePlusY P r) •
        ∑ j ∈ Finset.range k,
          A (r.matrixRank - k + j) * cyclicGeneratorMatrix P r ^ j := by sorry
