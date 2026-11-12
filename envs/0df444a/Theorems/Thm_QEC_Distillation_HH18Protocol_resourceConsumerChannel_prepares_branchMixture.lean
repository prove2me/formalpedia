-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_resourceConsumerChannel_prepares_branchMixture
-- name    : QEC.Distillation.HH18Protocol.resourceConsumerChannel_prepares_branchMixture
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:08:32.289768+00:00
-- url     : https://prove2.me/theorems/c6f33041-791c-4d7f-a5a8-75c600549742
-- title:
--   HH18 Protocol: resource Consumer Channel prepares branch Mixture
-- statement:
--   The resource consumer maps the actual finite measured-resource distribution
--   to the corresponding physical sitewise-injection branch mixture.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/ResourceChannel.lean#L47-L62
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/ResourceChannel.lean#L47-L62

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_ResourceDiagonal
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_ResourceChannel
import Theorems.Thm_QEC_Distillation_HH18Protocol_errorBranchState_normSq

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Protocol
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
universe u
attribute [local instance] QEC.Distillation.HH18Protocol.instChannelClassicalDecidable
set_option maxHeartbeats 4000000
set_option maxRecDepth 262144

theorem QEC.Distillation.HH18Protocol.resourceConsumerChannel_prepares_branchMixture
    (inputs : ResourceInput resourceCount QubitSpace) :
    resourceConsumerChannel (prepareMeasuredResources inputs).toOperator =
      physicalErrorWords.sum (fun error =>
        (measuredErrorWordProbability inputs error : Complex) •
          (DensityOperator.pureDensity (errorBranchState error)
            (errorBranchState_normSq error)).toOperator) := by sorry
