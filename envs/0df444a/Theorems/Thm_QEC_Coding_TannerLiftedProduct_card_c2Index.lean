-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_c2Index
-- name    : QEC.Coding.TannerLiftedProduct.card_c2Index
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:12:36.981759+00:00
-- url     : https://prove2.me/theorems/f9665eea-0c0c-4279-9be4-b2cccbdc272e
-- title:
--   Tanner Lifted Product: card c2 Index
-- statement:
--   Exact degree-two endpoint cell count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLiftedProduct.lean#L141-L145
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLiftedProduct.lean#L141-L145

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
omit [Field F] [Fintype F] [Group G] [DecidableEq G] [DecidableEq W]
    [Fintype R] [DecidableEq R] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.card_c2Index :
    Fintype.card (LiftedProduct.C2Index W (Fin 2 × R') G) =
      2 * Fintype.card R' * Fintype.card W * Fintype.card G := by sorry
