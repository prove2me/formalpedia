-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_verticalDirectionsInto_add_outside
-- name    : QEC.Coding.TannerLiftedProduct.card_verticalDirectionsInto_add_outside
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:39:54.435679+00:00
-- url     : https://prove2.me/theorems/ce7c32d4-595b-4cbe-967e-493287c03b9a
-- title:
--   Tanner Lifted Product: card vertical Directions Into add outside
-- statement:
--   The incoming and outside vertical directions partition all directions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGlobalExpansion.lean#L100-L108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGlobalExpansion.lean#L100-L108

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
omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq W] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.card_verticalDirectionsInto_add_outside
    (label : W → G) (L : Finset (VertexIndex G)) (v : VertexIndex G) :
    (verticalDirectionsInto label L v).card +
        (verticalDirectionsOutside label L v).card = Fintype.card W := by sorry
