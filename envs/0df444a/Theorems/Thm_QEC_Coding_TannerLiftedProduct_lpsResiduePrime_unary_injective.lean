-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrime_unary_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsResiduePrime_unary_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:00:26.408595+00:00
-- url     : https://prove2.me/theorems/ae660503-f43f-4875-991b-b71f870e4a2a
-- title:
--   Tanner Lifted Product: lps Residue Prime unary injective
-- statement:
--   All non-q residue-prime data are proofs, so unary q faithfully identifies the source parameter.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSquareRootMachine.lean#L31-L39
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSquareRootMachine.lean#L31-L39

import Definitions.Def_QEC_Coding_BitTuring_UnarySquareRoot
import Definitions.Def_QEC_Coding_BitTuring_UnarySquareRootInput
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSquareRootMachine
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsResiduePrime_unary_injective (p : ℕ) :
    Function.Injective (fun a:LPSResiduePrime p => unary a.q) := by sorry
