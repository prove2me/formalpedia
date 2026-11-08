-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_boundary2Matrix_eq_zero_of_not_mem_supportCover
-- name    : QEC.Coding.TannerLiftedProduct.boundary2Matrix_eq_zero_of_not_mem_supportCover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:33:48.396899+00:00
-- url     : https://prove2.me/theorems/fd4badd3-4b6f-4eeb-8f61-8389b125a43d
-- title:
--   Tanner Lifted Product: boundary2 Matrix eq zero of not mem support Cover
-- statement:
--   Outside the explicit Tanner support cover, a second-boundary matrix row
--   vanishes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L318-L339
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L318-L339

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

theorem QEC.Coding.TannerLiftedProduct.boundary2Matrix_eq_zero_of_not_mem_supportCover
    (label : W → G) (h : Matrix R W F) (h' : Matrix R' W F)
    (q : LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)
    (c2 : LiftedProduct.C2Index W (Fin 2 × R') G)
    (hq : q ∉ boundary2SupportCover label h h' c2) :
    LiftedProduct.boundary2Matrix (data label h h') q c2 = 0 := by sorry
