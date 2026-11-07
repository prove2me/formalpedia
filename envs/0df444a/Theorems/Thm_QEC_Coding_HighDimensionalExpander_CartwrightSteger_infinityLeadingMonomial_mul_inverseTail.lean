-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityLeadingMonomial_mul_inverseTail
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityLeadingMonomial_mul_inverseTail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:03:21.45523+00:00
-- url     : https://prove2.me/theorems/31a287f2-0658-4374-8920-8646b412b8d0
-- title:
--   Cartwright Steger: infinity Leading Monomial mul inverse Tail
-- statement:
--   Expand the leading monomial against the inverse tail using the skew
--   relation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L770-L808
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L770-L808

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityLeadingMonomial_mul_inverseTail
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k : ℕ) (ζ : ConstantExtension P r) :
    infinityLeadingMonomial P r k ζ *
        constantConjugatedBInverseTail P r u =
      ∑ i ∈ Finset.range r.matrixRank,
        constantMatrix P r
            (ζ * (constantFrobenius P r ^ k)
              (infinityCyclicCoefficient P r u i : ConstantExtension P r)) *
          cyclicGeneratorMatrix P r ^ (k + i) := by sorry
