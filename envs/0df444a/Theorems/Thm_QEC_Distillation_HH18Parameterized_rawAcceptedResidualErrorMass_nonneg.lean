-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_rawAcceptedResidualErrorMass_nonneg
-- name    : QEC.Distillation.HH18Parameterized.rawAcceptedResidualErrorMass_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:03:00.745599+00:00
-- url     : https://prove2.me/theorems/bfaa5228-c97a-47b5-b633-5f86fe4c62da
-- title:
--   HH18 Parameterized: raw Accepted Residual Error Mass nonneg
-- statement:
--   The HH18 Parameterized construction uses the raw Accepted Residual Error Mass nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SuccessResidual.lean#L117-L125
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SuccessResidual.lean#L117-L125

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PhysicalEndpoint
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SuccessResidual
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Parameterized.instSuccessClassicalDecidable

theorem QEC.Distillation.HH18Parameterized.rawAcceptedResidualErrorMass_nonneg (w r m : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    0 ≤ rawAcceptedResidualErrorMass w r m epsilon := by sorry
