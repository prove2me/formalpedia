-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_measuredErrorWordProbability_noisyResources
-- name    : QEC.Distillation.HH18Protocol.measuredErrorWordProbability_noisyResources
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:52:47.144906+00:00
-- url     : https://prove2.me/theorems/dc1867db-ca74-4852-8aff-9378b49e0d2c
-- title:
--   HH18 Protocol: measured Error Word Probability noisy Resources
-- statement:
--   Measuring the literal independent HH18 resource family gives precisely
--   the product Bernoulli law of its physical diagonal-error word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/ResourcePreparation.lean#L202-L221
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/ResourcePreparation.lean#L202-L221

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhysicalTypes
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Postselection
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_ResourcePreparation
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Protocol
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Protocol.instClassicalDecidable

theorem QEC.Distillation.HH18Protocol.measuredErrorWordProbability_noisyResources
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (error : PhysicalErrorWord) :
    measuredErrorWordProbability (noisyResources epsilon) error =
      HH18NoisyInput.errorWordWeight epsilon error := by sorry
