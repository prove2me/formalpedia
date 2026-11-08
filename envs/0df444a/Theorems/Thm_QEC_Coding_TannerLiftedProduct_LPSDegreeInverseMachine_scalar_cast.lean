-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSDegreeInverseMachine_scalar_cast
-- name    : QEC.Coding.TannerLiftedProduct.LPSDegreeInverseMachine.scalar_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:56:58.228045+00:00
-- url     : https://prove2.me/theorems/8fb3dc5d-b7bd-4c95-8727-404fd27ec7d9
-- title:
--   LPSDegree Inverse Machine: scalar cast
-- statement:
--   The canonical returned scalar casts to the exact original field inverse.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSInverseMachine.lean#L56-L57
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSInverseMachine.lean#L56-L57

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldInverse
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSquareRootMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSInverseMachine
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSDegreeInverseMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition

theorem QEC.Coding.TannerLiftedProduct.LPSDegreeInverseMachine.scalar_cast {p:ℕ} (a:LPSResiduePrime p) :
    (scalar a:ZMod a.q)=(lpsEffectiveDegreeRoot a)⁻¹ := by sorry
