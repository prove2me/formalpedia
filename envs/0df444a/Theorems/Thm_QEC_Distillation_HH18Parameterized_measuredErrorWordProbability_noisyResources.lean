-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_measuredErrorWordProbability_noisyResources
-- name    : QEC.Distillation.HH18Parameterized.measuredErrorWordProbability_noisyResources
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:44:20.154597+00:00
-- url     : https://prove2.me/theorems/0d2ce032-f07e-4c4f-bb00-ba55a9b70354
-- title:
--   HH18 Parameterized: measured Error Word Probability noisy Resources
-- statement:
--   Measuring the literal independent parameterized inverse-T resource family
--   recovers its exact product Bernoulli error-word law.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/ResourceMeasurement.lean#L171-L189
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/ResourceMeasurement.lean#L171-L189

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Preparation
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhaseInjection
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_ResourceMeasurement
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

theorem QEC.Distillation.HH18Parameterized.measuredErrorWordProbability_noisyResources (m w : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (error : PhysicalErrorWord m w) :
    measuredErrorWordProbability m w (noisyResources m w epsilon) error =
      HH18NoisyInput.errorWordWeight epsilon error := by sorry
