-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSLDeterminantMachine_predicate_eq_candidate
-- name    : QEC.Coding.TannerLiftedProduct.LPSSLDeterminantMachine.predicate_eq_candidate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:02:26.395234+00:00
-- url     : https://prove2.me/theorems/f693160e-0a75-4603-9815-006eabe2e9d8
-- title:
--   LPSSLDeterminant Machine: predicate eq candidate
-- statement:
--   Actual finite instructions or proved determinant invariant, whole budget or source certificate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSLDeterminantMachine.lean#L47-L54
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSLDeterminantMachine.lean#L47-L54

import Definitions.Def_QEC_Coding_BitTuring_UnaryDeterminantPredicate
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSMatrixProductMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSLDeterminantMachine
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSLDeterminantMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition FieldProjection
open QEC.Coding.BitTuring.UnaryArithmetic.DeterminantPredicate

theorem QEC.Coding.TannerLiftedProduct.LPSSLDeterminantMachine.predicate_eq_candidate (q:ℕ) (hq:1<q) (a b c d:Fin q) :
    decide (result a.val b.val c.val d.val q=1)=
      (QEC.Coding.TannerLiftedProduct.lpsSLMatrixCandidate q a b c d).isSome := by sorry
