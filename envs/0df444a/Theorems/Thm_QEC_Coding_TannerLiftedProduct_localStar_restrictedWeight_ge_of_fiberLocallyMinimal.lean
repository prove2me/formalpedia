-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_localStar_restrictedWeight_ge_of_fiberLocallyMinimal
-- name    : QEC.Coding.TannerLiftedProduct.localStar_restrictedWeight_ge_of_fiberLocallyMinimal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:48:42.96588+00:00
-- url     : https://prove2.me/theorems/f3e5510a-3006-4186-ba30-2f525812a2af
-- title:
--   Tanner Lifted Product: local Star restricted Weight ge of fiber Locally Minimal
-- statement:
--   Concrete PK22 active-vertex star bound. Once both inactive-direction sets
--   are large, an active vertex supplies a nonzero product-kernel witness; the
--   J2/J3 dichotomy then forces at least s active faces in their rectangle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L1575-L1634
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L1575-L1634

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

theorem QEC.Coding.TannerLiftedProduct.localStar_restrictedWeight_ge_of_fiberLocallyMinimal
    (label : W → G) (h : Matrix R W F)
    (hRank : h.rank = Fintype.card R) (g' : Matrix R' W F)
    (gInjective : Function.Injective
      (fun u : Word F R' => g'.transpose.mulVec u))
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hcCycle : LiftedProduct.boundary1 (data label h g') c = 0)
    (hcLocal : LocallyMinimalDistance.IsLocallyMinimal blockWeight
      (horizontalFiberBoundaryMoves label h g') c)
    (v : VertexIndex G) (hv : localVertexMatrix c v ≠ 0)
    (d m s : Nat) (beta : ℝ)
    (hExpand : ProductExpansion.ProductExpanding h
      (ProductExpansion.generatorImageParityCheck g') s (2 * m) beta)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hHorizontalLarge : Fintype.card W - m <
      (horizontalInactiveDirections label c v).card)
    (hVerticalLarge : Fintype.card W - m <
      (verticalInactiveDirections label c v).card)
    (hDistanceScale : 4 * m ≤ d)
    (hRectangleScale : 4 * s ≤ m * d)
    (hBudget : 4 * (m : ℝ) + 2 ≤ beta * Fintype.card W) :
    s ≤ ProductExpansion.restrictedWeight (localFaceMatrix label c v)
      (verticalInactiveDirections label c v)
      (horizontalInactiveDirections label c v) := by sorry
