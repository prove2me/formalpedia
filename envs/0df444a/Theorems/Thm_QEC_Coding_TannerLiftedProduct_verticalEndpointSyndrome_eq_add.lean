-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_verticalEndpointSyndrome_eq_add
-- name    : QEC.Coding.TannerLiftedProduct.verticalEndpointSyndrome_eq_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:37:30.206578+00:00
-- url     : https://prove2.me/theorems/0e3864aa-f95c-48c3-af8a-b76e8816b27b
-- title:
--   Tanner Lifted Product: vertical Endpoint Syndrome eq add
-- statement:
--   The two endpoint contributions split into the distinguished vertex and
--   its vertical neighbor, with the exact Tanner coordinate conventions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L438-L457
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L438-L457

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
omit [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq G]
    [Fintype W] [DecidableEq W] [Fintype R] [DecidableEq R]
    [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.verticalEndpointSyndrome_eq_add
    (label : W → G) (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) :
    verticalEndpointSyndrome label h' c v =
      verticalVertexSyndrome h' c v +
        verticalNeighborSyndrome label h' c v := by sorry
