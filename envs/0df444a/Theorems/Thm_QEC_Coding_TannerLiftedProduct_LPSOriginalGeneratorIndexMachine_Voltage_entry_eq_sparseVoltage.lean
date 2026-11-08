-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSOriginalGeneratorIndexMachine_Voltage_entry_eq_sparseVoltage
-- name    : QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Voltage.entry_eq_sparseVoltage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:59:00.861027+00:00
-- url     : https://prove2.me/theorems/edf310be-8007-497c-8748-d04deae2889b
-- title:
--   Voltage: entry eq sparse Voltage
-- statement:
--   Each exact table field equals the existing sparse-CSS voltage index.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGeneratorVoltageMachine.lean#L151-L157
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGeneratorVoltageMachine.lean#L151-L157

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGeneratorIndexMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGeneratorVoltageMachine
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Voltage
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Voltage._p2m_local_instance_ef31e85fec_23

theorem QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Voltage.entry_eq_sparseVoltage {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (side:Fin 2) (j:Fin D):
 (entries a (List.ofFn g))[(fieldIndex side j).val]'(by rw [entries_length,List.length_ofFn]; exact (fieldIndex side j).isLt)=
 (lpsSparseVoltage (fun j=>result a (g j)) side j).val:= by sorry
