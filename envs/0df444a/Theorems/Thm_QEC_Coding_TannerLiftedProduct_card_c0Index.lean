-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_c0Index
-- name    : QEC.Coding.TannerLiftedProduct.card_c0Index
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:12:33.253405+00:00
-- url     : https://prove2.me/theorems/887a79dd-7a76-4795-afbe-111784923bc6
-- title:
--   Tanner Lifted Product: card c0 Index
-- statement:
--   Exact degree-zero endpoint cell count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLiftedProduct.lean#L132-L136
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLiftedProduct.lean#L132-L136

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
    [DecidableEq R] [Fintype R'] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.card_c0Index :
    Fintype.card (LiftedProduct.C0Index (Fin 2 × R) W G) =
      2 * Fintype.card R * Fintype.card W * Fintype.card G := by sorry
