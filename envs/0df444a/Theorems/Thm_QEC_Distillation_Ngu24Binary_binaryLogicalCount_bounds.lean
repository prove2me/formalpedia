-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryLogicalCount_bounds
-- name    : QEC.Distillation.Ngu24Binary.binaryLogicalCount_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:59:33.707594+00:00
-- url     : https://prove2.me/theorems/b4e22d6c-d515-4272-8c9c-60d36431b74f
-- title:
--   Ngu24 Binary: binary Logical Count bounds
-- statement:
--   The Ngu24 Binary construction uses the binary Logical Count bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryParameters.lean#L95-L106
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryParameters.lean#L95-L106

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

theorem QEC.Distillation.Ngu24Binary.binaryLogicalCount_bounds (i : Nat) :
    (binaryLength i : ℚ) / 10240 ≤ f256MultiplicationLogicalCount i ∧
      (f256MultiplicationLogicalCount i : ℚ) ≤ binaryLength i := by sorry
