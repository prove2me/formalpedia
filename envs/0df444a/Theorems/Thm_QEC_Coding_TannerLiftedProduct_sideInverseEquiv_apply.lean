-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_sideInverseEquiv_apply
-- name    : QEC.Coding.TannerLiftedProduct.sideInverseEquiv_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:01:25.996354+00:00
-- url     : https://prove2.me/theorems/8b34c0a2-cb1b-4778-bba2-717fe46b110d
-- title:
--   Tanner Lifted Product: side Inverse Equiv apply
-- statement:
--   The Tanner Lifted Product construction uses the side Inverse Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L141-L142
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L141-L142

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe v
variable {G W : Type v}
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
omit [Fintype G] [DecidableEq G]

theorem QEC.Coding.TannerLiftedProduct.sideInverseEquiv_apply (x : Fin 2 × G) :
    sideInverseEquiv x = (oppositeSide x.1, x.2⁻¹) := by sorry

attribute [defeq] QEC.Coding.TannerLiftedProduct.sideInverseEquiv_apply
