-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_qubitIndex
-- name    : QEC.Coding.TannerLiftedProduct.card_qubitIndex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:13:26.16636+00:00
-- url     : https://prove2.me/theorems/a340fc6b-c0da-459f-abc4-e11889eb341c
-- title:
--   Tanner Lifted Product: card qubit Index
-- statement:
--   Exact physical coordinate count of the Tanner lifted product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLiftedProduct.lean#L119-L127
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLiftedProduct.lean#L119-L127

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldCSSPresentation
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Theorems.Thm_QEC_Coding_LiftedProduct_card_qubitIndex

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
omit [Field F] [Fintype F] [Group G] [DecidableEq G] [DecidableEq W]
    [DecidableEq R] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.card_qubitIndex :
    Fintype.card
        (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G) =
      Fintype.card G *
        (Fintype.card W * Fintype.card W +
          4 * Fintype.card R * Fintype.card R') := by sorry
