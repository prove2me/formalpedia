-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_sum_infinityShiftedCorrectionTerm
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.sum_infinityShiftedCorrectionTerm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:03:58.540455+00:00
-- url     : https://prove2.me/theorems/c2cca85d-5d9e-4299-b77d-961848b2c128
-- title:
--   Cartwright Steger: sum infinity Shifted Correction Term
-- statement:
--   Rotating the full cyclic correction sum by a basis exponent `k`
--   produces the unshifted full sum and one extra `y` times its first `k`
--   terms.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L1100-L1152
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L1100-L1152

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.sum_infinityShiftedCorrectionTerm
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k : ℕ) (hk : k ≤ r.matrixRank) (ζ : ConstantExtension P r) :
    (∑ i ∈ Finset.range r.matrixRank,
        infinityShiftedCorrectionTerm P r u k i ζ) =
      infinityConjugationCorrectionSum P r u k r.matrixRank ζ +
        (splittingY P r) •
          infinityConjugationCorrectionSum P r u k k ζ := by sorry
