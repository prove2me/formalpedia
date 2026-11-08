-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_verticalNeighborSyndrome_row_eq_zero_of_mem_inactive
-- name    : QEC.Coding.TannerLiftedProduct.verticalNeighborSyndrome_row_eq_zero_of_mem_inactive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:38:10.410766+00:00
-- url     : https://prove2.me/theorems/ec2beeba-031d-4ba5-9909-d97a647a09e8
-- title:
--   Tanner Lifted Product: vertical Neighbor Syndrome row eq zero of mem inactive
-- statement:
--   On an inactive vertical direction, the opposite-endpoint syndrome
--   vanishes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L683-L693
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L683-L693

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
omit [Fintype F] [Fintype G] [DecidableEq G] [DecidableEq W]
    [DecidableEq R] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.verticalNeighborSyndrome_row_eq_zero_of_mem_inactive
    (label : W → G) (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) (b : W)
    (hb : b ∈ verticalInactiveDirections label c v) :
    verticalNeighborSyndrome label h' c v b = 0 := by sorry
