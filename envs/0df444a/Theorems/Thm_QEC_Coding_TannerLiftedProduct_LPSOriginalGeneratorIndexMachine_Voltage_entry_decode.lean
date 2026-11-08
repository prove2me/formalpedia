-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSOriginalGeneratorIndexMachine_Voltage_entry_decode
-- name    : QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Voltage.entry_decode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:57:48.13721+00:00
-- url     : https://prove2.me/theorems/26cb1303-ee9e-4daf-a6ac-1ca467c6df2b
-- title:
--   Voltage: entry decode
-- statement:
--   Computed sparse voltages decode to the original source double-cover group labels.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGeneratorVoltageMachine.lean#L159-L163
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGeneratorVoltageMachine.lean#L159-L163

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGeneratorIndexMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGeneratorVoltageMachine
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Voltage
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Voltage._p2m_local_instance_ef31e85fec_23

theorem QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Voltage.entry_decode {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (side:Fin 2) (j:Fin D):
 (lpsPSLEnumerationEquiv a.q) (lpsSparseVoltage (fun j=>result a (g j)) side j)=
 doubleCoverVoltage (fun j=>lpsQuaternionLabel a (g j)) side j:= by sorry
