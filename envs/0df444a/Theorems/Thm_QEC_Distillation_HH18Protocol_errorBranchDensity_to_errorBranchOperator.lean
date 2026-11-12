-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_errorBranchDensity_to_errorBranchOperator
-- name    : QEC.Distillation.HH18Protocol.errorBranchDensity_to_errorBranchOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:10:34.278273+00:00
-- url     : https://prove2.me/theorems/34cf7734-8b98-4705-9a79-269d75d69d5e
-- title:
--   HH18 Protocol: error Branch Density to error Branch Operator
-- statement:
--   The pure physical branch density is exactly the syndrome-decoding branch
--   operator for the same measured error word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/ResourceConsumer.lean#L27-L33
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/ResourceConsumer.lean#L27-L33

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_ResourceChannel
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_ResourceConsumer
import Theorems.Thm_QEC_Distillation_HH18Protocol_errorBranchState_normSq

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Protocol
open Semantics
open Semantics.Qubit

theorem QEC.Distillation.HH18Protocol.errorBranchDensity_to_errorBranchOperator
    (error : PhysicalErrorWord) :
    (DensityOperator.pureDensity (errorBranchState error)
      (errorBranchState_normSq error)).toOperator =
      HH18SyndromeDecoding.errorBranchOperator error := by sorry
