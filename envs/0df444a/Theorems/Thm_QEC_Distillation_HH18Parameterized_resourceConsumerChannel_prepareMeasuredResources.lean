-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_resourceConsumerChannel_prepareMeasuredResources
-- name    : QEC.Distillation.HH18Parameterized.resourceConsumerChannel_prepareMeasuredResources
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:54:20.097179+00:00
-- url     : https://prove2.me/theorems/9221c7d4-7ae9-465f-afbb-7d1687b49a6e
-- title:
--   HH18 Parameterized: resource Consumer Channel prepare Measured Resources
-- statement:
--   The actual measured resource record is mapped linearly to the matching
--   mixture of actual physical error branches over the same named support.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/ResourceConsumer.lean#L202-L220
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/ResourceConsumer.lean#L202-L220

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_ResourceMeasurement
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_ResourceConsumerSupport
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_ResourceConsumer
import Theorems.Thm_QEC_Distillation_HH18Parameterized_errorBranchState_normSq

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
universe u
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Parameterized.instConsumerClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Parameterized.instConsumerClassicalDecidable

theorem QEC.Distillation.HH18Parameterized.resourceConsumerChannel_prepareMeasuredResources {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (inputs : ResourceInput (physicalInputCount m w) QubitSpace) :
    resourceConsumerChannel h hdegree
      (prepareMeasuredResources m w inputs).toOperator =
      (physicalErrorWords m w).sum (fun error =>
        (measuredErrorWordProbability m w inputs error : Complex) •
          (DensityOperator.pureDensity (errorBranchState h hdegree error)
            (errorBranchState_normSq h hdegree error)).toOperator) := by sorry
