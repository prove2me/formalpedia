-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_boundary1RowSupport_subset_cover
-- name    : QEC.Coding.TannerLiftedProduct.boundary1RowSupport_subset_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:13:00.643544+00:00
-- url     : https://prove2.me/theorems/31b785d1-c206-4bd6-84b1-8762f1db13ba
-- title:
--   Tanner Lifted Product: boundary1 Row Support subset cover
-- statement:
--   Every nonzero coordinate in a first-boundary row lies in its explicit
--   group-size-independent cover.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLiftedProduct.lean#L238-L279
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLiftedProduct.lean#L238-L279

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

theorem QEC.Coding.TannerLiftedProduct.boundary1RowSupport_subset_cover
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (c0 : LiftedProduct.C0Index (Fin 2 × R) W G) :
    LiftedProduct.boundary1RowSupport (data label h g') c0 ⊆
      boundary1SupportCover label h g' c0 := by sorry
