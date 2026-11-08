-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResidueX_zero_of_residuePrime
-- name    : QEC.Coding.TannerLiftedProduct.lpsResidueX_zero_of_residuePrime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:59:43.236161+00:00
-- url     : https://prove2.me/theorems/3c265250-a419-4f2a-8719-8fd28b104b36
-- title:
--   Tanner Lifted Product: lps Residue X zero of residue Prime
-- statement:
--   The original source residue-pair first coordinate is zero at an LPS residue prime.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSquareRootMachine.lean#L205-L208
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSquareRootMachine.lean#L205-L208

import Definitions.Def_QEC_Coding_BitTuring_UnarySquareRoot
import Definitions.Def_QEC_Coding_BitTuring_UnarySquareRootInput
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSquareRootMachine
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsResidueX_zero_of_residuePrime (a : LPSResiduePrime p) : lpsResidueX a.q=0 := by sorry
