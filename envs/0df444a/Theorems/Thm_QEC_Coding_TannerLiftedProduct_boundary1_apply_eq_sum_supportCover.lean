-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_boundary1_apply_eq_sum_supportCover
-- name    : QEC.Coding.TannerLiftedProduct.boundary1_apply_eq_sum_supportCover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:37:54.035027+00:00
-- url     : https://prove2.me/theorems/d464b0ea-7c81-46b0-9ec4-5c1865e67c7f
-- title:
--   Tanner Lifted Product: boundary1 apply eq sum support Cover
-- statement:
--   Evaluation of the first boundary may be restricted exactly to its
--   group-size-independent Tanner support cover.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L343-L357
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L343-L357

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

theorem QEC.Coding.TannerLiftedProduct.boundary1_apply_eq_sum_supportCover
    (label : W → G) (h : Matrix R W F) (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (c0 : LiftedProduct.C0Index (Fin 2 × R) W G) :
    LiftedProduct.boundary1 (data label h h') c c0 =
      ∑ q ∈ boundary1SupportCover label h h' c0,
        LiftedProduct.boundary1Matrix (data label h h') c0 q * c q := by sorry
