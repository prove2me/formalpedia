-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_selectedLogicalPortComplementIdealState_apply
-- name    : QEC.Distillation.HH18Parameterized.selectedLogicalPortComplementIdealState_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:45:58.198193+00:00
-- url     : https://prove2.me/theorems/8d3c598b-848c-4c0a-a23f-b1ab3a148318
-- title:
--   HH18 Parameterized: selected Logical Port Complement Ideal State apply
-- statement:
--   The HH18 Parameterized construction uses the selected Logical Port Complement Ideal State apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SelectedPort.lean#L101-L108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SelectedPort.lean#L101-L108

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedErrorBridge
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SelectedPortSupport
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SelectedPort
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
attribute [local instance] QEC.Distillation.HH18Parameterized.instSelectedPortClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Parameterized.instSelectedPortClassicalDecidable

theorem QEC.Distillation.HH18Parameterized.selectedLogicalPortComplementIdealState_apply (m w : Nat)
    (port : LogicalSite m w)
    (bits : Qubit.Bitstring (selectedLogicalPortSubsystem m w port).ComplementCoordinates) :
    selectedLogicalPortComplementIdealState m w port bits =
      (Real.sqrt 2 : Complex) *
        Triorthogonal.BinaryRowFamily.logicalMagicState (LogicalSite m w)
          (selectedLogicalPortAnchorBitstring m w port bits) := by sorry

attribute [defeq] QEC.Distillation.HH18Parameterized.selectedLogicalPortComplementIdealState_apply
