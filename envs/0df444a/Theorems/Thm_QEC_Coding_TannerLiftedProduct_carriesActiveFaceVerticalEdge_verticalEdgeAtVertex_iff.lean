-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_carriesActiveFaceVerticalEdge_verticalEdgeAtVertex_iff
-- name    : QEC.Coding.TannerLiftedProduct.carriesActiveFaceVerticalEdge_verticalEdgeAtVertex_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:03:28.411204+00:00
-- url     : https://prove2.me/theorems/d40cf377-343b-4bd0-83da-a913637edac3
-- title:
--   Tanner Lifted Product: carries Active Face Vertical Edge vertical Edge At Vertex iff
-- statement:
--   Carrying an active face is independent of the endpoint used to name the
--   physical vertical edge.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L638-L651
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L638-L651

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGlobalExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
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

theorem QEC.Coding.TannerLiftedProduct.carriesActiveFaceVerticalEdge_verticalEdgeAtVertex_iff
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) (b : W) :
    CarriesActiveFaceVerticalEdge label c
        (verticalEdgeAtVertex label v b) ↔
      CarriesActiveFaceVerticalEdgeAt label c v b := by sorry
