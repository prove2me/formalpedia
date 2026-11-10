-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryDistance_detects
-- name    : QEC.Distillation.Ngu24Binary.binaryDistance_detects
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:56:29.344829+00:00
-- url     : https://prove2.me/theorems/8e9506cd-7ab2-4309-bd48-cb5f5ce2964a
-- title:
--   Ngu24 Binary: binary Distance detects
-- statement:
--   The Ngu24 Binary construction uses the binary Distance detects property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryParameters.lean#L62-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryParameters.lean#L62-L64

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

theorem QEC.Distillation.Ngu24Binary.binaryDistance_detects (i : Nat) :
    QuditSubsystem.BPTMeasurementDistance (binaryEncodedCode i).code (binaryDistance i) := by sorry
