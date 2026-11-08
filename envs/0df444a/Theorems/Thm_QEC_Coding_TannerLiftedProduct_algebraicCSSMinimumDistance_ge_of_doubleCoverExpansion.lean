-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_algebraicCSSMinimumDistance_ge_of_doubleCoverExpansion
-- name    : QEC.Coding.TannerLiftedProduct.algebraicCSSMinimumDistance_ge_of_doubleCoverExpansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:43:37.553206+00:00
-- url     : https://prove2.me/theorems/d8f4cf5a-a652-46e7-a459-13a99353df89
-- title:
--   Tanner Lifted Product: algebraic CSSMinimum Distance ge of double Cover Expansion
-- statement:
--   The two product-expansion orientations and one labelled double-cover
--   expansion bound give the attained algebraic CSS distance of the Tanner lifted
--   product.  This is the distance-level PK22 interface: the remaining family
--   theorem only has to instantiate its finite-field and graph hypotheses.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L1194-L1245
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L1194-L1245

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProductDuality
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerTranspose
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.algebraicCSSMinimumDistance_ge_of_doubleCoverExpansion
    (label : W → G) (h : Matrix R W F) (h' : Matrix R' W F)
    (hRank : h.rank = Fintype.card R)
    (h'Injective : Function.Injective
      (fun u : Word F R' => h'.transpose.mulVec u))
    (h'Rank : h'.rank = Fintype.card R')
    (hInjective : Function.Injective
      (fun u : Word F R => h.transpose.mulVec u))
    (d m s : Nat) (beta : ℝ)
    (hProductExpand : ProductExpansion.ProductExpanding h
      (ProductExpansion.generatorImageParityCheck h') s (2 * m) beta)
    (hProductExpandReverse : ProductExpansion.ProductExpanding h'
      (ProductExpansion.generatorImageParityCheck h) s (2 * m) beta)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hDistanceReverse : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h').carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hLength : d ≤ Fintype.card W)
    (hTwo : 2 ≤ Fintype.card W) (hFour : 4 ≤ d)
    (hDistanceScale : 4 * m ≤ d)
    (hRectangleScale : 4 * s ≤ m * d)
    (hBudget : 4 * (m : ℝ) + 2 ≤ beta * Fintype.card W)
    (radius : Nat) (lambda : ℝ) (hLambda : 0 < lambda)
    (hBase : SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph label) radius lambda)
    (hVerticalThreshold : (2 * m : ℝ) + lambda ≤ d)
    (hEdgeThreshold : 2 * (2 * lambda) ≤ m)
    (hFaceThreshold :
      2 * (((Nat.log 2 (2 * Fintype.card W) + 1 : Nat) : ℝ) *
        (8 * lambda ^ 2)) ≤ s)
    (dCSS : Nat)
    (hMinimum : AlgebraicCSSMinimumDistance
      (chainComplex label h h').firstCoboundaryCheckCode
      (chainComplex label h h').middleBoundaryCode dCSS) :
    radius / (2 * Fintype.card W) + 1 ≤ dCSS := by sorry
