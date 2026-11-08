-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_activeVertex_edge_or_face_expanding
-- name    : QEC.Coding.TannerLiftedProduct.activeVertex_edge_or_face_expanding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:40:37.562196+00:00
-- url     : https://prove2.me/theorems/8ac94da4-782d-4c2c-9a89-d58cd151371e
-- title:
--   Tanner Lifted Product: active Vertex edge or face expanding
-- statement:
--   A concrete active vertex either has at least `m` labelled neighbours in
--   the product graph or at least `s` active-face paths to labelled vertices in
--   the face-square graph.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGlobalExpansion.lean#L281-L344
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGlobalExpansion.lean#L281-L344

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

theorem QEC.Coding.TannerLiftedProduct.activeVertex_edge_or_face_expanding
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
    (hOpposite : ∀ v ∈ vertexBlockSupport c,
      ∀ a ∈ horizontalDirectionsOutside label L v,
      ∀ b ∈ verticalDirectionsOutside label L v,
      localFaceMatrix label c v b a ≠ 0 →
        verticalNeighbor label (horizontalNeighbor label v a) b ∈ L)
    (v : VertexIndex G) (hv : v ∈ vertexBlockSupport c)
    (d m s : Nat) (beta : ℝ)
    (hExpand : ProductExpansion.ProductExpanding h
      (ProductExpansion.generatorImageParityCheck g') s (2 * m) beta)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hLength : d ≤ Fintype.card W)
    (hDistanceScale : 4 * m ≤ d)
    (hRectangleScale : 4 * s ≤ m * d)
    (hBudget : 4 * (m : ℝ) + 2 ≤ beta * Fintype.card W) :
    m ≤ ∑ u ∈ L, adjacencyGraph label v u ∨
      s ≤ ∑ u ∈ L, faceSquareGraph label v u := by sorry
