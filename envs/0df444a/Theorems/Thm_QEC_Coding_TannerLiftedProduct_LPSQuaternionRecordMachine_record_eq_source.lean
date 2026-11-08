-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSQuaternionRecordMachine_record_eq_source
-- name    : QEC.Coding.TannerLiftedProduct.LPSQuaternionRecordMachine.record_eq_source
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:32:03.662779+00:00
-- url     : https://prove2.me/theorems/88a4287a-1028-4804-889a-74cfea3b5a49
-- title:
--   LPSQuaternion Record Machine: record eq source
-- statement:
--   All seven record fields are exact original source data, in the documented retention order.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionRecordMachine.lean#L234-L238
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionRecordMachine.lean#L234-L238

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

theorem QEC.Coding.TannerLiftedProduct.LPSQuaternionRecordMachine.record_eq_source {p:ℕ} (a:LPSResiduePrime p) (t:LPSQuaternion) :
    record a t=stream ([((lpsEffectiveDegreeRoot a)⁻¹).val,(lpsResidueY a.q).val]++
      (coordinates a t).reverse++[a.q]) := by sorry
