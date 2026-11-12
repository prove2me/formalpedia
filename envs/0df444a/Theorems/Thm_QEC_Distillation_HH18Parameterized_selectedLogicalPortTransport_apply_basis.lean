-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_selectedLogicalPortTransport_apply_basis
-- name    : QEC.Distillation.HH18Parameterized.selectedLogicalPortTransport_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:46:01.413924+00:00
-- url     : https://prove2.me/theorems/9150c9ee-2320-4f1b-a8c7-acf2f8ca925f
-- title:
--   HH18 Parameterized: selected Logical Port Transport apply basis
-- statement:
--   The HH18 Parameterized construction uses the selected Logical Port Transport apply basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SelectedPort.lean#L78-L86
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SelectedPort.lean#L78-L86

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

theorem QEC.Distillation.HH18Parameterized.selectedLogicalPortTransport_apply_basis (m w : Nat)
    (port : LogicalSite m w)
    (bits : Qubit.Bitstring (selectedLogicalPortSubsystem m w port).SelectedCoordinates) :
    selectedLogicalPortTransport m w port
      (EuclideanSpace.basisFun _ Complex bits) =
      EuclideanSpace.basisFun _ Complex
        (selectedLogicalPortBitstringEquiv m w port bits) := by sorry
