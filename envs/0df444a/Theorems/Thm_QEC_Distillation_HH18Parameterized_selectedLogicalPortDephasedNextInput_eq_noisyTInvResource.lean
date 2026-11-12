-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_selectedLogicalPortDephasedNextInput_eq_noisyTInvResource
-- name    : QEC.Distillation.HH18Parameterized.selectedLogicalPortDephasedNextInput_eq_noisyTInvResource
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:06:41.699599+00:00
-- url     : https://prove2.me/theorems/5eb544a7-4018-437a-821a-93c96123d3f8
-- title:
--   HH18 Parameterized: selected Logical Port Dephased Next Input eq noisy TInv Resource
-- statement:
--   The actual inverse-transported, dephased selected output is exactly the
--   noisy inverse-T resource at its explicitly domain-certified measured rate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DepthTwoRouting.lean#L123-L136
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DepthTwoRouting.lean#L123-L136

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

theorem QEC.Distillation.HH18Parameterized.selectedLogicalPortDephasedNextInput_eq_noisyTInvResource {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon port ≤ 1 / 2) :
    selectedLogicalPortDephasedNextInput h hdegree epsilon port =
      HH18NoisyInput.noisyTInvResource
        (selectedLogicalPortNextInputRate h hdegree epsilon port hhalf) := by sorry
