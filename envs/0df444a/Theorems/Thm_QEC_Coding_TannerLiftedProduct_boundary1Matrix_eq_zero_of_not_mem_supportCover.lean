-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_boundary1Matrix_eq_zero_of_not_mem_supportCover
-- name    : QEC.Coding.TannerLiftedProduct.boundary1Matrix_eq_zero_of_not_mem_supportCover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:38:27.082532+00:00
-- url     : https://prove2.me/theorems/ffb4405b-d480-404b-bbbf-1d25edf6c99a
-- title:
--   Tanner Lifted Product: boundary1 Matrix eq zero of not mem support Cover
-- statement:
--   Outside the explicit Tanner support cover, a first-boundary matrix row
--   vanishes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L293-L314
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L293-L314

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

theorem QEC.Coding.TannerLiftedProduct.boundary1Matrix_eq_zero_of_not_mem_supportCover
    (label : W → G) (h : Matrix R W F) (h' : Matrix R' W F)
    (c0 : LiftedProduct.C0Index (Fin 2 × R) W G)
    (q : LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)
    (hq : q ∉ boundary1SupportCover label h h' c0) :
    LiftedProduct.boundary1Matrix (data label h h') c0 q = 0 := by sorry
