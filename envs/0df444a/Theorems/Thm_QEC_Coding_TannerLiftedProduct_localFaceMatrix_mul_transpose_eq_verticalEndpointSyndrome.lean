-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_localFaceMatrix_mul_transpose_eq_verticalEndpointSyndrome
-- name    : QEC.Coding.TannerLiftedProduct.localFaceMatrix_mul_transpose_eq_verticalEndpointSyndrome
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:37:54.521195+00:00
-- url     : https://prove2.me/theorems/5373e1b4-3f96-4e17-991a-5fe0177a0f34
-- title:
--   Tanner Lifted Product: local Face Matrix mul transpose eq vertical Endpoint Syndrome
-- statement:
--   A global one-cycle restricts at every vertex to the exact row-syndrome
--   equation used to choose the PK22 coset-leader matrix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L593-L604
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L593-L604

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

theorem QEC.Coding.TannerLiftedProduct.localFaceMatrix_mul_transpose_eq_verticalEndpointSyndrome
    (label : W → G) (h : Matrix R W F) (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hc : LiftedProduct.boundary1 (data label h h') c = 0)
    (v : VertexIndex G) :
    localFaceMatrix label c v * h.transpose =
      verticalEndpointSyndrome label h' c v := by sorry
