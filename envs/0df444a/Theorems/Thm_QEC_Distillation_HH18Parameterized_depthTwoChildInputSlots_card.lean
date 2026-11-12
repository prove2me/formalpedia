-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_depthTwoChildInputSlots_card
-- name    : QEC.Distillation.HH18Parameterized.depthTwoChildInputSlots_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:12:40.782939+00:00
-- url     : https://prove2.me/theorems/8432c772-c118-4af3-9802-e41a656bbd62
-- title:
--   HH18 Parameterized: depth Two Child Input Slots card
-- statement:
--   The exact number of actual child-input slots in the transposed grid.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DepthTwoRouting.lean#L66-L69
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DepthTwoRouting.lean#L66-L69

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

theorem QEC.Distillation.HH18Parameterized.depthTwoChildInputSlots_card (m w : Nat) :
    Fintype.card (depthTwoChildInputSlots m w) =
      logicalOutputCount m w * physicalInputCount m w := by sorry
