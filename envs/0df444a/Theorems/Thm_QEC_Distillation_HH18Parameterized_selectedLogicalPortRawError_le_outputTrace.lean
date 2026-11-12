-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_selectedLogicalPortRawError_le_outputTrace
-- name    : QEC.Distillation.HH18Parameterized.selectedLogicalPortRawError_le_outputTrace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:06:33.462214+00:00
-- url     : https://prove2.me/theorems/6ab07026-1a48-485d-832a-fce1c8928724
-- title:
--   HH18 Parameterized: selected Logical Port Raw Error le output Trace
-- statement:
--   The HH18 Parameterized construction uses the selected Logical Port Raw Error le output Trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SelectedPort.lean#L515-L534
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SelectedPort.lean#L515-L534

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

theorem QEC.Distillation.HH18Parameterized.selectedLogicalPortRawError_le_outputTrace {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (port : LogicalSite m w) :
    selectedLogicalPortRawError h hdegree epsilon port ≤
      outputTraceError
        (resourceDecodedRun h hdegree (noisyResources m w epsilon)).acceptedOutput
        (idealLogicalTOutput m w) := by sorry
