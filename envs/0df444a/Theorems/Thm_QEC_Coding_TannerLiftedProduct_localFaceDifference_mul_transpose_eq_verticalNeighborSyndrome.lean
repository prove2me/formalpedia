-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_localFaceDifference_mul_transpose_eq_verticalNeighborSyndrome
-- name    : QEC.Coding.TannerLiftedProduct.localFaceDifference_mul_transpose_eq_verticalNeighborSyndrome
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:37:57.946203+00:00
-- url     : https://prove2.me/theorems/b0197f0a-dcf7-443e-817b-5e24c5a18125
-- title:
--   Tanner Lifted Product: local Face Difference mul transpose eq vertical Neighbor Syndrome
-- statement:
--   A cycle's face/coset-leader difference has exactly the syndrome supplied
--   by the opposite vertical endpoints.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L662-L677
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L662-L677

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

theorem QEC.Coding.TannerLiftedProduct.localFaceDifference_mul_transpose_eq_verticalNeighborSyndrome
    (label : W → G) (h : Matrix R W F)
    (hRank : h.rank = Fintype.card R) (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hc : LiftedProduct.boundary1 (data label h h') c = 0)
    (v : VertexIndex G) :
    localFaceDifference label h hRank h' c v * h.transpose =
      verticalNeighborSyndrome label h' c v := by sorry
