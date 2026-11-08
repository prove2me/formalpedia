-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSQuaternionRecordMachine_original_matrix_fields
-- name    : QEC.Coding.TannerLiftedProduct.LPSQuaternionRecordMachine.original_matrix_fields
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:31:51.563725+00:00
-- url     : https://prove2.me/theorems/923c34c6-1402-4b24-874f-5ca95d2f42c8
-- title:
--   LPSQuaternion Record Machine: original matrix fields
-- statement:
--   Exact original matrix coordinate convention to be consumed by the next actual assembly.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionRecordMachine.lean#L243-L249
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionRecordMachine.lean#L243-L249

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

theorem QEC.Coding.TannerLiftedProduct.LPSQuaternionRecordMachine.original_matrix_fields {p:ℕ} (a:LPSResiduePrime p) (t:LPSQuaternion) :
    LPSMatrixProductMachine.fields a.q (lpsQuaternionMatrix a.q t)=
      [((t.a:ZMod a.q)+(t.d:ZMod a.q)*lpsResidueY a.q).val,
       (-(t.b:ZMod a.q)*lpsResidueY a.q+(t.c:ZMod a.q)).val,
       (-(t.b:ZMod a.q)*lpsResidueY a.q-(t.c:ZMod a.q)).val,
       ((t.a:ZMod a.q)-(t.d:ZMod a.q)*lpsResidueY a.q).val] := by sorry
