-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryDistance_bounds
-- name    : QEC.Distillation.Ngu24Binary.binaryDistance_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:58:14.475544+00:00
-- url     : https://prove2.me/theorems/5a5cfa1b-b5ad-4d66-a029-f0aed60ff2a7
-- title:
--   Ngu24 Binary: binary Distance bounds
-- statement:
--   The Ngu24 Binary construction uses the binary Distance bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryParameters.lean#L108-L119
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryParameters.lean#L108-L119

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

theorem QEC.Distillation.Ngu24Binary.binaryDistance_bounds (i : Nat) :
    (binaryLength i : ℚ) / 5120 ≤ binaryDistance i ∧
      (binaryDistance i : ℚ) ≤ binaryLength i := by sorry
