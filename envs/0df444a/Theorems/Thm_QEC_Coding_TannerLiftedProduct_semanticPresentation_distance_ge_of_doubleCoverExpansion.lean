-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_semanticPresentation_distance_ge_of_doubleCoverExpansion
-- name    : QEC.Coding.TannerLiftedProduct.semanticPresentation_distance_ge_of_doubleCoverExpansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:47:13.857283+00:00
-- url     : https://prove2.me/theorems/322e63c5-9f11-4686-b240-ba0a84bb94ad
-- title:
--   Tanner Lifted Product: semantic Presentation distance ge of double Cover Expansion
-- statement:
--   The deterministic PK22 hypotheses give the same graph-radius lower bound
--   on the actual semantic finite-qudit distance whenever the Tanner product has
--   positive encoded dimension.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerSemanticDistance.lean#L150-L196
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerSemanticDistance.lean#L150-L196

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionPairProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerTranspose
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerSemanticDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u
variable {F G W R R' : Type u}
variable [Field F] [Fintype F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_138d9bf296_23
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_138d9bf296_24

theorem QEC.Coding.TannerLiftedProduct.semanticPresentation_distance_ge_of_doubleCoverExpansion
    (label : W → G) (h : Matrix R W F) (h' : Matrix R' W F)
    (hRank : h.rank = Fintype.card R)
    (h'Rank : h'.rank = Fintype.card R')
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
    (hHomologyPositive : 0 < Module.finrank F
      (chainComplex label h h').middleHomology) :
    radius / (2 * Fintype.card W) + 1 ≤
      (semanticPresentation label h h').distance := by sorry
