-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJDilatedQuotient_nonconstant
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJDilatedQuotient_nonconstant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:27:51.324221+00:00
-- url     : https://prove2.me/theorems/e05bd706-b7ce-4855-a644-075aa6a5a368
-- title:
--   Tanner Lifted Product: lps Original JDilated Quotient nonconstant
-- statement:
--   The original descended j(Ntau) quotient function is nonconstant; used by the root fixture and the forthcoming original j/jN function-field equation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDilatedModularFunction.lean#L116-L119
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDilatedModularFunction.lean#L116-L119

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJDilatedQuotient_nonconstant (N : ℕ) (hN : 0<N) :
    ¬∃ c : ℂ, ∀ x, lpsOriginalJDilatedQuotient N hN x=c := by sorry
