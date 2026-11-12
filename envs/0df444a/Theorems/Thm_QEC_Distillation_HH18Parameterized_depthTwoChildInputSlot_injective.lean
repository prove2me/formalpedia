-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_depthTwoChildInputSlot_injective
-- name    : QEC.Distillation.HH18Parameterized.depthTwoChildInputSlot_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:06:45.397299+00:00
-- url     : https://prove2.me/theorems/709fcee1-411f-42c0-98d2-8bcecce5e10d
-- title:
--   HH18 Parameterized: depth Two Child Input Slot injective
-- statement:
--   A fixed child receives its physical inputs from pairwise distinct parent
--   indices.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DepthTwoRouting.lean#L83-L89
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DepthTwoRouting.lean#L83-L89

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

theorem QEC.Distillation.HH18Parameterized.depthTwoChildInputSlot_injective (m w : Nat)
    (child : LogicalSite m w) :
    Function.Injective (depthTwoChildInputSlot m w child) := by sorry
