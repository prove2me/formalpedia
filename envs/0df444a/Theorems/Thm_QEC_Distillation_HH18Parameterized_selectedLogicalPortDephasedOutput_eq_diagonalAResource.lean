-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_selectedLogicalPortDephasedOutput_eq_diagonalAResource
-- name    : QEC.Distillation.HH18Parameterized.selectedLogicalPortDephasedOutput_eq_diagonalAResource
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:47:13.634968+00:00
-- url     : https://prove2.me/theorems/14fabba3-25c8-440f-966c-c46000acecec
-- title:
--   HH18 Parameterized: selected Logical Port Dephased Output eq diagonal AResource
-- statement:
--   The HH18 Parameterized construction uses the selected Logical Port Dephased Output eq diagonal AResource property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SelectedPort.lean#L473-L480
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SelectedPort.lean#L473-L480

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

theorem QEC.Distillation.HH18Parameterized.selectedLogicalPortDephasedOutput_eq_diagonalAResource {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (port : LogicalSite m w) :
    selectedLogicalPortDephasedOutput h hdegree epsilon port =
      diagonalAResource (selectedLogicalPortRawParameter h hdegree epsilon port) := by sorry
