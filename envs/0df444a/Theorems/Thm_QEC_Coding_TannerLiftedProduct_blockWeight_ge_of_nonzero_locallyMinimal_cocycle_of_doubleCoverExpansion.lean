-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_blockWeight_ge_of_nonzero_locallyMinimal_cocycle_of_doubleCoverExpansion
-- name    : QEC.Coding.TannerLiftedProduct.blockWeight_ge_of_nonzero_locallyMinimal_cocycle_of_doubleCoverExpansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:43:01.149602+00:00
-- url     : https://prove2.me/theorems/87637719-15be-4846-86e0-335687dc6514
-- title:
--   Tanner Lifted Product: block Weight ge of nonzero locally Minimal cocycle of double Cover Expansion
-- statement:
--   A nonzero vertically fiber-minimal cocycle has the same block-weight
--   lower bound, using the reverse product-expansion orientation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L1133-L1188
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L1133-L1188

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

theorem QEC.Coding.TannerLiftedProduct.blockWeight_ge_of_nonzero_locallyMinimal_cocycle_of_doubleCoverExpansion
    (label : W → G) (h : Matrix R W F) (h' : Matrix R' W F)
    (hRank : h'.rank = Fintype.card R')
    (hInjective : Function.Injective
      (fun u : Word F R => h.transpose.mulVec u))
    (z : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hzCocycle : z ∈ (chainComplex label h h').middleCocycleCode.carrier)
    (hzNonzero : z ≠ 0)
    (hzLocal : LocallyMinimalDistance.IsLocallyMinimal blockWeight
      (verticalFiberCoboundaryMoves label h h') z)
    (d m s : Nat) (beta : ℝ)
    (hProductExpand : ProductExpansion.ProductExpanding h'
      (ProductExpansion.generatorImageParityCheck h) s (2 * m) beta)
    (hDistance : ∀ x : Word F W,
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
        (8 * lambda ^ 2)) ≤ s) :
    radius / (2 * Fintype.card W) + 1 ≤ blockWeight z := by sorry
