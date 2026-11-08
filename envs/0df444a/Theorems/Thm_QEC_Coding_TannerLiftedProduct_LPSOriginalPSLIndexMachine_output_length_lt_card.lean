-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSOriginalPSLIndexMachine_output_length_lt_card
-- name    : QEC.Coding.TannerLiftedProduct.LPSOriginalPSLIndexMachine.output_length_lt_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:42:12.744266+00:00
-- url     : https://prove2.me/theorems/fd045ce2-d374-4df1-9c00-ea163beb045f
-- title:
--   LPSOriginal PSLIndex Machine: output length lt card
-- statement:
--   Original unary index length is strictly below the genuine PSL carrier size.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPSLIndexMachine.lean#L380-L387
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPSLIndexMachine.lean#L380-L387

import Definitions.Def_QEC_Coding_BitTuring_CountedFlagLoop
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLListMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLIndexMachine
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSOriginalPSLIndexMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition
open QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalPSLIndexMachine._p2m_local_instance_70373be6ef_345

theorem QEC.Coding.TannerLiftedProduct.LPSOriginalPSLIndexMachine.output_length_lt_card (a:Input):(output a).length<Fintype.card PSL(2,ZMod a.1.val):= by sorry
