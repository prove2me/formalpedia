-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_cycle_eq_zero_of_doubleCoverExpansion
-- name    : QEC.Coding.TannerLiftedProduct.cycle_eq_zero_of_doubleCoverExpansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:16:06.838998+00:00
-- url     : https://prove2.me/theorems/526e5b86-12e7-4d76-9759-66039dd5ea8e
-- title:
--   Tanner Lifted Product: cycle eq zero of double Cover Expansion
-- statement:
--   Source-shaped one-orientation PK22 zero lemma whose graph hypotheses have
--   all been discharged from one small-set expansion bound on the labelled Cayley
--   double cover.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L819-L871
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L819-L871

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe v
variable {G W : Type v}
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
universe u
variable {F : Type u} {R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.cycle_eq_zero_of_doubleCoverExpansion
    (label : W → G) (h : Matrix R W F)
    (hRank : h.rank = Fintype.card R) (g' : Matrix R' W F)
    (gInjective : Function.Injective
      (fun u : Word F R' => g'.transpose.mulVec u))
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hcCycle : LiftedProduct.boundary1 (data label h g') c = 0)
    (hcLocal : LocallyMinimalDistance.IsLocallyMinimal blockWeight
      (horizontalFiberBoundaryMoves label h g') c)
    (d m s : Nat) (beta : ℝ)
    (hProductExpand : ProductExpansion.ProductExpanding h
      (ProductExpansion.generatorImageParityCheck g') s (2 * m) beta)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hLength : d ≤ Fintype.card W)
    (hTwo : 2 ≤ Fintype.card W) (hFour : 4 ≤ d)
    (hDistanceScale : 4 * m ≤ d)
    (hRectangleScale : 4 * s ≤ m * d)
    (hBudget : 4 * (m : ℝ) + 2 ≤ beta * Fintype.card W)
    (radius : Nat) (lambda : ℝ) (hLambda : 0 < lambda)
    (hBase : SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph label) radius lambda)
    (hBlockRadiusVertical :
      Fintype.card W * blockWeight c ≤ radius)
    (hBlockRadiusEdge : blockWeight c ≤ radius)
    (hBlockRadiusFace :
      blockWeight c ≤ radius / (2 * Fintype.card W))
    (hVerticalThreshold : (2 * m : ℝ) + lambda ≤ d)
    (hEdgeThreshold : 2 * (2 * lambda) ≤ m)
    (hFaceThreshold :
      2 * (((Nat.log 2 (2 * Fintype.card W) + 1 : Nat) : ℝ) *
        (8 * lambda ^ 2)) ≤ s) :
    c = 0 := by sorry
