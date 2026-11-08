-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_variableSupport_subset_cover
-- name    : QEC.Coding.TannerLiftedProduct.variableSupport_subset_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:12:35.446916+00:00
-- url     : https://prove2.me/theorems/347c0694-d901-4f7d-83bd-f6f395c5bf3a
-- title:
--   Tanner Lifted Product: variable Support subset cover
-- statement:
--   Every check incident to a qubit lies in its explicit
--   group-size-independent cover.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLiftedProduct.lean#L427-L512
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLiftedProduct.lean#L427-L512

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

theorem QEC.Coding.TannerLiftedProduct.variableSupport_subset_cover
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (q : LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G) :
    (LiftedProduct.boundaryIncidence (data label h g')).variableSupport q ⊆
      variableSupportCover label h g' q := by sorry
