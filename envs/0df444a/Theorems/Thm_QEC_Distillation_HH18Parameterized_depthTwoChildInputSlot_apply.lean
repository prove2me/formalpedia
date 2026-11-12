-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_depthTwoChildInputSlot_apply
-- name    : QEC.Distillation.HH18Parameterized.depthTwoChildInputSlot_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:51:09.10314+00:00
-- url     : https://prove2.me/theorems/d4c88d4d-990c-4110-8343-f5302911920c
-- title:
--   HH18 Parameterized: depth Two Child Input Slot apply
-- statement:
--   The HH18 Parameterized construction uses the depth Two Child Input Slot apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DepthTwoRouting.lean#L76-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DepthTwoRouting.lean#L76-L79

import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_ResourceMeasurement
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SelectedPort
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DepthTwoRouting
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
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.depthTwoChildInputSlot_apply (m w : Nat)
    (child : LogicalSite m w) (parent : Fin (physicalInputCount m w)) :
    depthTwoChildInputSlot m w child parent = (child, parent) := by sorry

attribute [defeq] QEC.Distillation.HH18Parameterized.depthTwoChildInputSlot_apply
