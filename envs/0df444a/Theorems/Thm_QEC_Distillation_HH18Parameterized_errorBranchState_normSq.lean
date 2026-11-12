-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_errorBranchState_normSq
-- name    : QEC.Distillation.HH18Parameterized.errorBranchState_normSq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:43:43.402205+00:00
-- url     : https://prove2.me/theorems/2d2bdab1-0ccc-4f4e-9b23-4e5b4dfeb04b
-- title:
--   HH18 Parameterized: error Branch State norm Sq
-- statement:
--   Every selected physical-error branch is normalized.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/ResourceMeasurement.lean#L244-L264
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/ResourceMeasurement.lean#L244-L264

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

theorem QEC.Distillation.HH18Parameterized.errorBranchState_normSq {w r m : Nat} (h : Admissible w r m)
    (hdegree : 3 * r < m) (error : PhysicalErrorWord m w) :
    ‖errorBranchState h hdegree error‖ ^ 2 = 1 := by sorry
