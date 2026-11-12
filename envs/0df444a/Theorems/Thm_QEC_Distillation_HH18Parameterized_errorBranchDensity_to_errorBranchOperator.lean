-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_errorBranchDensity_to_errorBranchOperator
-- name    : QEC.Distillation.HH18Parameterized.errorBranchDensity_to_errorBranchOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:58:05.904105+00:00
-- url     : https://prove2.me/theorems/5313c8cd-5d6f-44da-9790-b8b4e4fe56d8
-- title:
--   HH18 Parameterized: error Branch Density to error Branch Operator
-- statement:
--   The pure physical resource-consumer branch is exactly the syndrome-layer
--   operator for the same physical error word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PhysicalEndpoint.lean#L45-L52
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PhysicalEndpoint.lean#L45-L52

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Postselection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_ResourceConsumer
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_EndpointSupport
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PhysicalEndpoint
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
attribute [local instance] QEC.Distillation.HH18Parameterized.instEndpointClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Parameterized.instEndpointClassicalDecidable

theorem QEC.Distillation.HH18Parameterized.errorBranchDensity_to_errorBranchOperator {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (error : PhysicalErrorWord m w) :
    (DensityOperator.pureDensity (errorBranchState h hdegree error)
      (errorBranchState_normSq h hdegree error)).toOperator =
      errorBranchOperator h hdegree error := by sorry
