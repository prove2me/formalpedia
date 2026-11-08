-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_verticalInactiveDirections_eq_heavy_union_agreement
-- name    : QEC.Coding.TannerLiftedProduct.verticalInactiveDirections_eq_heavy_union_agreement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:35:32.186341+00:00
-- url     : https://prove2.me/theorems/49743ac1-3378-4dd2-883e-2be716d4c015
-- title:
--   Tanner Lifted Product: vertical Inactive Directions eq heavy union agreement
-- statement:
--   The heavy and agreement directions partition all inactive vertical
--   directions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L725-L738
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L725-L738

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
omit [Fintype F] [Fintype G] [DecidableEq G]
    [DecidableEq R] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.verticalInactiveDirections_eq_heavy_union_agreement
    (label : W → G) (h : Matrix R W F)
    (hRank : h.rank = Fintype.card R) (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) :
    verticalInactiveDirections label c v =
      localHeavyDifferenceDirections label h hRank h' c v ∪
        localAgreementDirections label h hRank h' c v := by sorry
