-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSDegreeInverseMachine_scalar_normalizes
-- name    : QEC.Coding.TannerLiftedProduct.LPSDegreeInverseMachine.scalar_normalizes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:17:33.813765+00:00
-- url     : https://prove2.me/theorems/292ae2df-c262-4ee8-b21e-50d640c169af
-- title:
--   LPSDegree Inverse Machine: scalar normalizes
-- statement:
--   The returned scalar is exactly the one in the original normalized SL matrix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSInverseMachine.lean#L60-L63
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSInverseMachine.lean#L60-L63

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldInverse
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSquareRootMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSInverseMachine
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSDegreeInverseMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition

theorem QEC.Coding.TannerLiftedProduct.LPSDegreeInverseMachine.scalar_normalizes {p:ℕ} (a:LPSResiduePrime p) (t:LPSQuaternion) (ht:t.norm=p) :
    (scalar a:ZMod a.q) • lpsQuaternionMatrix a.q t=(lpsEffectiveQuaternionSL a t ht).val := by sorry
