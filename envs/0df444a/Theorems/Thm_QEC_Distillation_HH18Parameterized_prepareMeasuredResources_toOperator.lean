-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_prepareMeasuredResources_toOperator
-- name    : QEC.Distillation.HH18Parameterized.prepareMeasuredResources_toOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:43:12.383088+00:00
-- url     : https://prove2.me/theorems/f6a8f06c-0fc1-4707-a1d4-eed187170312
-- title:
--   HH18 Parameterized: prepare Measured Resources to Operator
-- statement:
--   The HH18 Parameterized construction uses the prepare Measured Resources to Operator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/ResourceMeasurement.lean#L219-L225
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/ResourceMeasurement.lean#L219-L225

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

theorem QEC.Distillation.HH18Parameterized.prepareMeasuredResources_toOperator (m w : Nat)
    (inputs : ResourceInput (physicalInputCount m w) QubitSpace) :
    (prepareMeasuredResources m w inputs).toOperator =
      (physicalErrorWords m w).sum (fun error =>
        (measuredErrorWordProbability m w inputs error : Complex) •
          (errorWordBasisDensity m w error).toOperator) := by sorry
