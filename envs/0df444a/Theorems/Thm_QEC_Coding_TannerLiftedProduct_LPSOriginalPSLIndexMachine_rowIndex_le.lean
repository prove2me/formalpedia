-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSOriginalPSLIndexMachine_rowIndex_le
-- name    : QEC.Coding.TannerLiftedProduct.LPSOriginalPSLIndexMachine.rowIndex_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:50:00.559466+00:00
-- url     : https://prove2.me/theorems/2a2c8157-1cc7-4e9b-8cd6-a44b24baf8cb
-- title:
--   LPSOriginal PSLIndex Machine: row Index le
-- statement:
--   The generic search ordinal never exceeds its row count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPSLIndexMachine.lean#L27-L31
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPSLIndexMachine.lean#L27-L31

import Definitions.Def_QEC_Coding_BitTuring_CountedFlagLoop
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLListMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLIndexMachine
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSOriginalPSLIndexMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition
open QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalPSLIndexMachine._p2m_local_instance_70373be6ef_21

theorem QEC.Coding.TannerLiftedProduct.LPSOriginalPSLIndexMachine.rowIndex_le (q:ℕ) [Fact q.Prime] (A:SL(2,ZMod q)) (R:List SL(2,ZMod q)):
 rowIndex q A R≤ R.length:= by sorry
