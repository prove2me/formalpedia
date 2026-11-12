-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_depthTwoFreshParentDephasedOutput_eq_selectedLogicalPortDephasedOutput
-- name    : QEC.Distillation.HH18Parameterized.depthTwoFreshParentDephasedOutput_eq_selectedLogicalPortDephasedOutput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:08:03.97737+00:00
-- url     : https://prove2.me/theorems/8b46b1eb-b0a8-4194-8f90-85a6b7361796
-- title:
--   HH18 Parameterized: depth Two Fresh Parent Dephased Output eq selected Logical Port Dephased Output
-- statement:
--   The dephased output of an indexed parent is the literal selected-port
--   dephasing of the actual one-level parameterized parent run.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DepthTwoRouting.lean#L159-L165
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DepthTwoRouting.lean#L159-L165

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

theorem QEC.Distillation.HH18Parameterized.depthTwoFreshParentDephasedOutput_eq_selectedLogicalPortDephasedOutput
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (source : depthTwoParentOutputSlots m w) :
    depthTwoFreshParentDephasedOutput h hdegree epsilon source =
      selectedLogicalPortDephasedOutput h hdegree epsilon source.2 := by sorry
