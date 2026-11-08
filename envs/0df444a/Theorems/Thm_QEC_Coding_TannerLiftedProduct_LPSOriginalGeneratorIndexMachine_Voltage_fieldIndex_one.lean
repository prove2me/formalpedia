-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSOriginalGeneratorIndexMachine_Voltage_fieldIndex_one
-- name    : QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Voltage.fieldIndex_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:57:48.253035+00:00
-- url     : https://prove2.me/theorems/c87af623-2e13-41b5-8cca-8538c37287e1
-- title:
--   Voltage: field Index one
-- statement:
--   Side one selects precisely the corresponding ordered generator field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGeneratorVoltageMachine.lean#L149-L149
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGeneratorVoltageMachine.lean#L149-L149

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGeneratorIndexMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGeneratorVoltageMachine
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Voltage
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Voltage._p2m_local_instance_ef31e85fec_23

theorem QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Voltage.fieldIndex_one {D:ℕ} (j:Fin D):fieldIndex 1 j=⟨j.val+1,by omega⟩:= by sorry
