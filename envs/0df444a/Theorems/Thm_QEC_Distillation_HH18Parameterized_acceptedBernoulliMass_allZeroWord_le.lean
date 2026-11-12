-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_acceptedBernoulliMass_allZeroWord_le
-- name    : QEC.Distillation.HH18Parameterized.acceptedBernoulliMass_allZeroWord_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:59:18.573508+00:00
-- url     : https://prove2.me/theorems/42352782-782f-49f7-91f4-41a2d56f72ee
-- title:
--   HH18 Parameterized: accepted Bernoulli Mass all Zero Word le
-- statement:
--   The actual accepted Bernoulli mass contains its nonnegative all-zero
--   physical-error summand.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SuccessResidual.lean#L41-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SuccessResidual.lean#L41-L64

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

theorem QEC.Distillation.HH18Parameterized.acceptedBernoulliMass_allZeroWord_le {w r m : Nat}
    (_h : Admissible w r m) (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    (1 - epsilon.1) ^ physicalInputCount m w ≤
      acceptedBernoulliMass w r m epsilon := by sorry
