-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_acceptedBernoulliMass_pos
-- name    : QEC.Distillation.HH18Parameterized.acceptedBernoulliMass_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:00:30.134855+00:00
-- url     : https://prove2.me/theorems/1b34f9a1-b1e6-4fa7-bc24-0f3dde9880d5
-- title:
--   HH18 Parameterized: accepted Bernoulli Mass pos
-- statement:
--   The accepted physical Bernoulli mass is strictly positive throughout the
--   declared diagonal-noise domain.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SuccessResidual.lean#L68-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SuccessResidual.lean#L68-L74

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

theorem QEC.Distillation.HH18Parameterized.acceptedBernoulliMass_pos {w r m : Nat}
    (h : Admissible w r m) (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    0 < acceptedBernoulliMass w r m epsilon := by sorry
