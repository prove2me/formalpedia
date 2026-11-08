-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_algebraicCSSMinimumDistance_ge_of_blockLocallyMinimal_bounds
-- name    : QEC.Coding.TannerLiftedProduct.algebraicCSSMinimumDistance_ge_of_blockLocallyMinimal_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:49:25.353429+00:00
-- url     : https://prove2.me/theorems/e266c03e-6b5c-4a0e-9bae-981cfac79c8f
-- title:
--   Tanner Lifted Product: algebraic CSSMinimum Distance ge of block Locally Minimal bounds
-- statement:
--   Bounds proved using scalar-coordinate local moves imply the same lower
--   bound on the attained algebraic CSS minimum distance.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L1662-L1683
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L1662-L1683

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_LocallyMinimalDistance
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerBlockWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.algebraicCSSMinimumDistance_ge_of_blockLocallyMinimal_bounds
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (lowerBound d : Nat)
    (hcycles : ∀ c,
      c ∈ (chainComplex label h g').middleCycleCode.carrier → c ≠ 0 →
      LocallyMinimalDistance.IsLocallyMinimal blockWeight
        (LocallyMinimalDistance.elementaryBoundaryMoves
          (chainComplex label h g')) c →
      lowerBound ≤ blockWeight c)
    (hcocycles : ∀ c,
      c ∈ (chainComplex label h g').middleCocycleCode.carrier → c ≠ 0 →
      LocallyMinimalDistance.IsLocallyMinimal blockWeight
        (LocallyMinimalDistance.elementaryCoboundaryMoves
          (chainComplex label h g')) c →
      lowerBound ≤ blockWeight c)
    (hminimum : AlgebraicCSSMinimumDistance
      (chainComplex label h g').firstCoboundaryCheckCode
      (chainComplex label h g').middleBoundaryCode d) :
    lowerBound ≤ d := by sorry
