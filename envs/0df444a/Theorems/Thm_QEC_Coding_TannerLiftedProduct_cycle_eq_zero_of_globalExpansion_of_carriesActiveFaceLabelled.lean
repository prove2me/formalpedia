-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_cycle_eq_zero_of_globalExpansion_of_carriesActiveFaceLabelled
-- name    : QEC.Coding.TannerLiftedProduct.cycle_eq_zero_of_globalExpansion_of_carriesActiveFaceLabelled
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:40:53.347688+00:00
-- url     : https://prove2.me/theorems/7530c13d-e110-4c25-a85e-911781a8888d
-- title:
--   Tanner Lifted Product: cycle eq zero of global Expansion of carries Active Face Labelled
-- statement:
--   Inclusive edge-incidence form of the global zero lemma. The two face
--   conditions follow when every vertical edge carrying an active face has a
--   labelled endpoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGlobalExpansion.lean#L653-L712
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGlobalExpansion.lean#L653-L712

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

theorem QEC.Coding.TannerLiftedProduct.cycle_eq_zero_of_globalExpansion_of_carriesActiveFaceLabelled
    (label : W → G) (h : Matrix R W F)
    (hRank : h.rank = Fintype.card R) (g' : Matrix R' W F)
    (gInjective : Function.Injective
      (fun u : Word F R' => g'.transpose.mulVec u))
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hcCycle : LiftedProduct.boundary1 (data label h g') c = 0)
    (hcLocal : LocallyMinimalDistance.IsLocallyMinimal blockWeight
      (horizontalFiberBoundaryMoves label h g') c)
    (L : Finset (VertexIndex G))
    (hActive : vertexBlockSupport c ⊆ L)
    (hEdgeLabel : ∀ v b, CarriesActiveFaceVerticalEdgeAt label c v b →
      v ∈ L ∨ verticalNeighbor label v b ∈ L)
    (d m s : Nat) (beta : ℝ)
    (hNonactiveEdge : ∀ v ∈ L, v ∉ vertexBlockSupport c →
      m ≤ ∑ u ∈ L, adjacencyGraph label v u)
    (hExpand : ProductExpansion.ProductExpanding h
      (ProductExpansion.generatorImageParityCheck g') s (2 * m) beta)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hLength : d ≤ Fintype.card W)
    (hDistanceScale : 4 * m ≤ d)
    (hRectangleScale : 4 * s ≤ m * d)
    (hBudget : 4 * (m : ℝ) + 2 ≤ beta * Fintype.card W)
    (radiusEdge radiusFace : Nat) (lambdaEdge lambdaFace : ℝ)
    (hLambdaEdge : 0 < lambdaEdge) (hLambdaFace : 0 < lambdaFace)
    (hExpandEdge : SmallSetExpansion.IsSmallSetEdgeExpanding
      (adjacencyGraph label) radiusEdge lambdaEdge)
    (hExpandFace : SmallSetExpansion.IsSmallSetEdgeExpanding
      (faceSquareGraph label) radiusFace lambdaFace)
    (hLRadiusEdge : L.card ≤ radiusEdge)
    (hLRadiusFace : L.card ≤ radiusFace)
    (hThresholdEdge : 2 * lambdaEdge ≤ m)
    (hThresholdFace : 2 * lambdaFace ≤ s) :
    c = 0 := by sorry
