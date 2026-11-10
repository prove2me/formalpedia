-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryDistance_le_length
-- name    : QEC.Distillation.Ngu24Binary.binaryDistance_le_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:47:39.477996+00:00
-- url     : https://prove2.me/theorems/b0a98011-83f9-498c-a554-99968129edc1
-- title:
--   Ngu24 Binary: binary Distance le length
-- statement:
--   The Ngu24 Binary construction uses the binary Distance le length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryParameters.lean#L76-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryParameters.lean#L76-L79

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryDistance
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteMeasurementDistance
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryParameters
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open Filter
open scoped BigOperators Topology
attribute [local instance] QEC.Distillation.Ngu24Binary._p2m_local_instance_6d70a6dbef_22

theorem QEC.Distillation.Ngu24Binary.binaryDistance_le_length (i : Nat) : binaryDistance i ≤ binaryLength i := by sorry
