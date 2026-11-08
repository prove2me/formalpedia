-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_boundary2RowSupport_subset_cover
-- name    : QEC.Coding.TannerLiftedProduct.boundary2RowSupport_subset_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:12:34.824189+00:00
-- url     : https://prove2.me/theorems/9bfc84a4-2047-4194-b58a-32e298cbdc9d
-- title:
--   Tanner Lifted Product: boundary2 Row Support subset cover
-- statement:
--   Every nonzero coordinate in a second-boundary row lies in its explicit
--   group-size-independent cover.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLiftedProduct.lean#L321-L362
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLiftedProduct.lean#L321-L362

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

theorem QEC.Coding.TannerLiftedProduct.boundary2RowSupport_subset_cover
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (c2 : LiftedProduct.C2Index W (Fin 2 × R') G) :
    LiftedProduct.boundary2RowSupport (data label h g') c2 ⊆
      boundary2SupportCover label h g' c2 := by sorry
