-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSQuaternionRecordMachine_residue_index_eq_val
-- name    : QEC.Coding.TannerLiftedProduct.LPSQuaternionRecordMachine.residue_index_eq_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:02:35.707373+00:00
-- url     : https://prove2.me/theorems/d7ff28b5-05ad-4562-a5a3-f860c1129563
-- title:
--   LPSQuaternion Record Machine: residue index eq val
-- statement:
--   The actually selected original Y index is already its canonical field value.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionRecordMachine.lean#L226-L232
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionRecordMachine.lean#L226-L232

import Definitions.Def_QEC_Coding_BitTuring_UnarySignedCoefficient
import Definitions.Def_QEC_Coding_BitTuring_ModulusQuery
import Definitions.Def_QEC_Coding_BitTuring_BitDelimiters
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSInverseMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSMatrixProductMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionRecordMachine
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSQuaternionRecordMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition
open FieldProjection
open scoped MatrixGroups

theorem QEC.Coding.TannerLiftedProduct.LPSQuaternionRecordMachine.residue_index_eq_val {p:ℕ} (a:LPSResiduePrime p) :
    lpsEffectiveResiduePairIndex a.q=(lpsResidueY a.q).val := by sorry
