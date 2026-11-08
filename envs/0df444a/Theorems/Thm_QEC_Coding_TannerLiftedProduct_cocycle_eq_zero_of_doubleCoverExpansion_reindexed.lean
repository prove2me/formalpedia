-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_cocycle_eq_zero_of_doubleCoverExpansion_reindexed
-- name    : QEC.Coding.TannerLiftedProduct.cocycle_eq_zero_of_doubleCoverExpansion_reindexed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:43:33.912032+00:00
-- url     : https://prove2.me/theorems/f2706c9b-ea0e-43ac-aea0-f1064c6a385d
-- title:
--   Tanner Lifted Product: cocycle eq zero of double Cover Expansion reindexed
-- statement:
--   The Tanner Lifted Product construction uses the cocycle eq zero of double Cover Expansion reindexed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L855-L929
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L855-L929

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

theorem QEC.Coding.TannerLiftedProduct.cocycle_eq_zero_of_doubleCoverExpansion_reindexed
    (label targetLabel : W → G) (inverseDirection : W ≃ W)
    (hInverse : ∀ a, targetLabel (inverseDirection a) = (label a)⁻¹)
    (h : Matrix R W F) (h' : Matrix R' W F)
    (hRank : (reindexColumns inverseDirection h').rank = Fintype.card R')
    (hInjective : Function.Injective
      (fun u : Word F R =>
        (reindexColumns inverseDirection h).transpose.mulVec u))
    (z : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hzCocycle : z ∈ (chainComplex label h h').middleCocycleCode.carrier)
    (hzLocal : LocallyMinimalDistance.IsLocallyMinimal blockWeight
      (verticalFiberCoboundaryMoves label h h') z)
    (d m s : Nat) (beta : ℝ)
    (hProductExpand : ProductExpansion.ProductExpanding
      (reindexColumns inverseDirection h')
      (ProductExpansion.generatorImageParityCheck
        (reindexColumns inverseDirection h)) s (2 * m) beta)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode
        (reindexColumns inverseDirection h')).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hLength : d ≤ Fintype.card W)
    (hTwo : 2 ≤ Fintype.card W) (hFour : 4 ≤ d)
    (hDistanceScale : 4 * m ≤ d)
    (hRectangleScale : 4 * s ≤ m * d)
    (hBudget : 4 * (m : ℝ) + 2 ≤ beta * Fintype.card W)
    (radius : Nat) (lambda : ℝ) (hLambda : 0 < lambda)
    (hBase : SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph targetLabel) radius lambda)
    (hBlockRadiusVertical :
      Fintype.card W * blockWeight z ≤ radius)
    (hBlockRadiusEdge : blockWeight z ≤ radius)
    (hBlockRadiusFace :
      blockWeight z ≤ radius / (2 * Fintype.card W))
    (hVerticalThreshold : (2 * m : ℝ) + lambda ≤ d)
    (hEdgeThreshold : 2 * (2 * lambda) ≤ m)
    (hFaceThreshold :
      2 * (((Nat.log 2 (2 * Fintype.card W) + 1 : Nat) : ℝ) *
        (8 * lambda ^ 2)) ≤ s) :
    z = 0 := by sorry
