-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_transpose_boundary2_horizontalEdge_apply
-- name    : QEC.Coding.TannerLiftedProduct.transpose_boundary2_horizontalEdge_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:42:22.131231+00:00
-- url     : https://prove2.me/theorems/5e8ffed1-562d-45fc-92a8-1b88d2fcfa2a
-- title:
--   Tanner Lifted Product: transpose boundary2 horizontal Edge apply
-- statement:
--   The transpose of the second boundary is the horizontal-edge equation:
--   one complete face row plus the two endpoint vertex fibers.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L355-L394
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L355-L394

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

theorem QEC.Coding.TannerLiftedProduct.transpose_boundary2_horizontalEdge_apply
    (label : W → G) (h : Matrix R W F) (h' : Matrix R' W F)
    (z : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) (a : W) (r' : R') :
    wordLinearMapTranspose (LiftedProduct.boundary2 (data label h h')) z
        (horizontalEdgeCoordinate label v a r') =
      (∑ b, h' r' b *
        z (faceCoordinate (R := R) (R' := R')
          (faceAtVertex label v a b))) +
      ∑ endpoint : Fin 2 × R,
        h endpoint.2 a *
          z (horizontalEndpointCoordinate label v a
            endpoint.1 endpoint.2 r') := by sorry
