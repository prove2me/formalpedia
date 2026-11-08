-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSLDeterminantMachine_sourceInput_injective
-- name    : QEC.Coding.TannerLiftedProduct.LPSSLDeterminantMachine.sourceInput_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:02:34.94773+00:00
-- url     : https://prove2.me/theorems/a000bc9a-1398-4d0e-80aa-337df71aef16
-- title:
--   LPSSLDeterminant Machine: source Input injective
-- statement:
--   Actual finite instructions or proved determinant invariant, whole budget or source certificate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSLDeterminantMachine.lean#L61-L72
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSLDeterminantMachine.lean#L61-L72

import Definitions.Def_QEC_Coding_BitTuring_UnaryDeterminantPredicate
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSMatrixProductMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSLDeterminantMachine
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSLDeterminantMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition FieldProjection
open QEC.Coding.BitTuring.UnaryArithmetic.DeterminantPredicate

theorem QEC.Coding.TannerLiftedProduct.LPSSLDeterminantMachine.sourceInput_injective (q:ℕ):Function.Injective (sourceInput q):= by sorry
