-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_prepareMeasuredResources_toOperator
-- name    : QEC.Distillation.HH18Protocol.prepareMeasuredResources_toOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:51:27.993719+00:00
-- url     : https://prove2.me/theorems/c6b2f0a9-3fcb-48bf-be3a-6cf34a0a9397
-- title:
--   HH18 Protocol: prepare Measured Resources to Operator
-- statement:
--   The HH18 Protocol construction uses the prepare Measured Resources to Operator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/ResourcePreparation.lean#L248-L254
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/ResourcePreparation.lean#L248-L254

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

theorem QEC.Distillation.HH18Protocol.prepareMeasuredResources_toOperator
    (inputs : ResourceInput resourceCount QubitSpace) :
    (prepareMeasuredResources inputs).toOperator =
      physicalErrorWords.sum (fun error =>
        (measuredErrorWordProbability inputs error : Complex) •
          (errorWordBasisDensity error).toOperator) := by sorry
