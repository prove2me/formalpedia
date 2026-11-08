-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_middle_le_finrank_homology_add_endpoints
-- name    : QEC.Coding.TannerLiftedProduct.card_middle_le_finrank_homology_add_endpoints
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:13:15.96028+00:00
-- url     : https://prove2.me/theorems/948ad932-bc8d-41f2-875e-da1dc424b1fe
-- title:
--   Tanner Lifted Product: card middle le finrank homology add endpoints
-- statement:
--   The generic lifted-product rank-nullity estimate specialized to the
--   double-cover Tanner construction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLiftedProduct.lean#L160-L173
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLiftedProduct.lean#L160-L173

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldCSSPresentation
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.LiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.card_middle_le_finrank_homology_add_endpoints
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F) :
    Fintype.card G *
        (Fintype.card W ^ 2 + 4 * Fintype.card R * Fintype.card R') ≤
      Module.finrank F (LiftedProduct.chainComplex (data label h g')).middleHomology +
        2 * Fintype.card R * Fintype.card W * Fintype.card G +
        2 * Fintype.card R' * Fintype.card W * Fintype.card G := by sorry
