-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSOriginalPSLListMachine_original_source
-- name    : QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.original_source
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:31:36.928233+00:00
-- url     : https://prove2.me/theorems/89705d7f-4f7a-48cd-94d6-67ae54694979
-- title:
--   LPSOriginal PSLList Machine: original source
-- statement:
--   Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPSLListMachine.lean#L336-L338
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPSLListMachine.lean#L336-L338

import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldRowsFilter
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPSLSearchMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSLListMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLListMachine
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine._p2m_local_instance_e75c5360c0_308

theorem QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.original_source (a:Input):
 (QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine.representatives a.val (lpsSLList a.val)).map (QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine.quotient a.val)=lpsPSLList a.val:= by sorry
