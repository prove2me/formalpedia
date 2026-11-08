-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_restrictedWeight_le_sum_faceSquareGraph
-- name    : QEC.Coding.TannerLiftedProduct.restrictedWeight_le_sum_faceSquareGraph
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:39:56.592724+00:00
-- url     : https://prove2.me/theorems/6854f242-8f1e-4012-be99-d81d26354e3b
-- title:
--   Tanner Lifted Product: restricted Weight le sum face Square Graph
-- statement:
--   If every active face in a selected rectangle has its opposite vertex in
--   `L`, its rectangle weight is bounded by outgoing face-square multiplicity
--   into `L`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGlobalExpansion.lean#L160-L178
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGlobalExpansion.lean#L160-L178

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
omit [Fintype F] [Fintype G] [DecidableEq W]
    [Fintype R] [DecidableEq R] [Fintype R'] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.restrictedWeight_le_sum_faceSquareGraph
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) (A B : Finset W)
    (L : Finset (VertexIndex G))
    (hOpposite : ∀ a ∈ A, ∀ b ∈ B,
      localFaceMatrix label c v b a ≠ 0 →
        verticalNeighbor label (horizontalNeighbor label v a) b ∈ L) :
    ProductExpansion.restrictedWeight (localFaceMatrix label c v) B A ≤
      ∑ u ∈ L, faceSquareGraph label v u := by sorry
