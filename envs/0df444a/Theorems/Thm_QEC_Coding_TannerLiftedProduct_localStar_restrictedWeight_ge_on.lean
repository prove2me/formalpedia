-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_localStar_restrictedWeight_ge_on
-- name    : QEC.Coding.TannerLiftedProduct.localStar_restrictedWeight_ge_on
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:40:51.425467+00:00
-- url     : https://prove2.me/theorems/3c17a4e9-a2ae-4677-90ed-39abf98818da
-- title:
--   Tanner Lifted Product: local Star restricted Weight ge on
-- statement:
--   The active-vertex local-star estimate on caller-selected large direction
--   sets. The vertical set only needs to consist of inactive opposite endpoints;
--   this form is what the global labelled-set argument consumes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGlobalExpansion.lean#L204-L276
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGlobalExpansion.lean#L204-L276

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerBlockWeight
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGlobalExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.localStar_restrictedWeight_ge_on
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
    (A B : Finset W)
    (hBInactive : B ⊆ verticalInactiveDirections label c v)
    (d m s : Nat) (beta : ℝ)
    (hExpand : ProductExpansion.ProductExpanding h
      (ProductExpansion.generatorImageParityCheck g') s (2 * m) beta)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hHorizontalLarge : Fintype.card W - m < A.card)
    (hVerticalLarge : Fintype.card W - m < B.card)
    (hDistanceScale : 4 * m ≤ d)
    (hRectangleScale : 4 * s ≤ m * d)
    (hBudget : 4 * (m : ℝ) + 2 ≤ beta * Fintype.card W) :
    s ≤ ProductExpansion.restrictedWeight (localFaceMatrix label c v) B A := by sorry
