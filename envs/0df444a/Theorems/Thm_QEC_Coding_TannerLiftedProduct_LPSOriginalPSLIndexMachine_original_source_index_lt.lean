-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSOriginalPSLIndexMachine_original_source_index_lt
-- name    : QEC.Coding.TannerLiftedProduct.LPSOriginalPSLIndexMachine.original_source_index_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:42:05.023353+00:00
-- url     : https://prove2.me/theorems/df97da1e-667f-4612-be2f-39e198cc3130
-- title:
--   LPSOriginal PSLIndex Machine: original source index lt
-- statement:
--   Original enumeration coverage rules out the missing-row sentinel.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPSLIndexMachine.lean#L131-L136
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPSLIndexMachine.lean#L131-L136

import Definitions.Def_QEC_Coding_BitTuring_CountedFlagLoop
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLListMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLIndexMachine
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSOriginalPSLIndexMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition
open QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalPSLIndexMachine._p2m_local_instance_70373be6ef_108

theorem QEC.Coding.TannerLiftedProduct.LPSOriginalPSLIndexMachine.original_source_index_lt (q:ℕ) [Fact q.Prime] (A:SL(2,ZMod q)):
 rowIndex q A (representatives q (lpsSLList q))<(representatives q (lpsSLList q)).length:= by sorry
