-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_oppositeVertex_mem_of_carriesActiveFace
-- name    : QEC.Coding.TannerLiftedProduct.oppositeVertex_mem_of_carriesActiveFace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:40:39.696543+00:00
-- url     : https://prove2.me/theorems/eb90a70d-446c-46b9-89fa-b2257a730181
-- title:
--   Tanner Lifted Product: opposite Vertex mem of carries Active Face
-- statement:
--   In an active-face rectangle whose horizontal neighbour is unlabelled, the
--   labelled endpoint of the opposite vertical edge is the diagonal vertex.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGlobalExpansion.lean#L558-L575
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGlobalExpansion.lean#L558-L575

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
omit [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq G]
    [Fintype W] [DecidableEq W] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.oppositeVertex_mem_of_carriesActiveFace
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (L : Finset (VertexIndex G))
    (hEdgeLabel : ∀ v b, CarriesActiveFaceVerticalEdgeAt label c v b →
      v ∈ L ∨ verticalNeighbor label v b ∈ L)
    (v : VertexIndex G) (a b : W)
    (ha : horizontalNeighbor label v a ∉ L)
    (hface : localFaceMatrix label c v b a ≠ 0) :
    verticalNeighbor label (horizontalNeighbor label v a) b ∈ L := by sorry
