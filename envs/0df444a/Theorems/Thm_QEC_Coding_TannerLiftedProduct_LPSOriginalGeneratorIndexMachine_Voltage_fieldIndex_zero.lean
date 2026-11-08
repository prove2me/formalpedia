-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSOriginalGeneratorIndexMachine_Voltage_fieldIndex_zero
-- name    : QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Voltage.fieldIndex_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:58:01.905805+00:00
-- url     : https://prove2.me/theorems/8b697cf9-2706-4c25-9b4b-bdc00de452c3
-- title:
--   Voltage: field Index zero
-- statement:
--   Side zero selects precisely the identity field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGeneratorVoltageMachine.lean#L147-L147
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGeneratorVoltageMachine.lean#L147-L147

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGeneratorIndexMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGeneratorVoltageMachine
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Voltage
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Voltage._p2m_local_instance_ef31e85fec_23

theorem QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Voltage.fieldIndex_zero {D:ℕ} (j:Fin D):fieldIndex 0 j=0:= by sorry
