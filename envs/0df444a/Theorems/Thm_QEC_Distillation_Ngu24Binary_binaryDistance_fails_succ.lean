-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryDistance_fails_succ
-- name    : QEC.Distillation.Ngu24Binary.binaryDistance_fails_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:58:22.345184+00:00
-- url     : https://prove2.me/theorems/c1ab7c24-c4a9-44a2-b007-1fcf28a28a03
-- title:
--   Ngu24 Binary: binary Distance fails succ
-- statement:
--   The Ngu24 Binary construction uses the binary Distance fails succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryParameters.lean#L66-L69
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryParameters.lean#L66-L69

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

theorem QEC.Distillation.Ngu24Binary.binaryDistance_fails_succ (i : Nat) :
    ¬ QuditSubsystem.BPTMeasurementDistance (binaryEncodedCode i).code (binaryDistance i + 1) := by sorry
