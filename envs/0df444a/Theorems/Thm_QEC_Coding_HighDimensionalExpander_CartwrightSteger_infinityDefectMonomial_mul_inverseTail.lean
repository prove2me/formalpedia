-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityDefectMonomial_mul_inverseTail
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityDefectMonomial_mul_inverseTail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:03:42.281938+00:00
-- url     : https://prove2.me/theorems/a622d81a-d0e0-4476-ae48-27ebbddbecbe
-- title:
--   Cartwright Steger: infinity Defect Monomial mul inverse Tail
-- statement:
--   Expand the predecessor defect against the inverse tail.  The inverse
--   skew relation contributes the literal `phi⁻¹` appearing in equation (9).
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L812-L886
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L812-L886

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityDefectMonomial_mul_inverseTail
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k : ℕ) (ζ : ConstantExtension P r) :
    infinityDefectMonomial P r u k ζ *
        constantConjugatedBInverseTail P r u =
      ∑ i ∈ Finset.range r.matrixRank,
        constantMatrix P r
            ((infinityCyclicInverseCoefficient P r u *
                (constantFrobenius P r).symm ζ) *
              (constantFrobenius P r).symm
                ((constantFrobenius P r ^ k)
                  (infinityCyclicCoefficient P r u i :
                    ConstantExtension P r))) *
          cyclicGeneratorInverseMatrix P r *
            cyclicGeneratorMatrix P r ^ (k + i) := by sorry
