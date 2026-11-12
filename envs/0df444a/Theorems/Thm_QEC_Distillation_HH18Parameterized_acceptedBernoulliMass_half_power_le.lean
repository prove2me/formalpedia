-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_acceptedBernoulliMass_half_power_le
-- name    : QEC.Distillation.HH18Parameterized.acceptedBernoulliMass_half_power_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:00:39.291117+00:00
-- url     : https://prove2.me/theorems/ee6c9993-3864-4cb2-b85d-01edb6aee089
-- title:
--   HH18 Parameterized: accepted Bernoulli Mass half power le
-- statement:
--   The all-zero summand gives a uniform accepted-mass lower bound on the
--   declared `0 ≤ ε ≤ 1/2` domain.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SuccessResidual.lean#L87-L96
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SuccessResidual.lean#L87-L96

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

theorem QEC.Distillation.HH18Parameterized.acceptedBernoulliMass_half_power_le {w r m : Nat}
    (h : Admissible w r m) (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    (1 / 2 : ℝ) ^ physicalInputCount m w ≤ acceptedBernoulliMass w r m epsilon := by sorry
