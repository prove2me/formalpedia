-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedErrorBranch_traceError_le_two
-- name    : QEC.Distillation.HH18Parameterized.decodedErrorBranch_traceError_le_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:04:24.214134+00:00
-- url     : https://prove2.me/theorems/c2881dac-5000-4337-b43b-3a7e6269f9cb
-- title:
--   HH18 Parameterized: decoded Error Branch trace Error le two
-- statement:
--   Every decoded physical-error branch is within trace norm two of the
--   ideal logical density.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedErrorBridge.lean#L75-L91
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedErrorBridge.lean#L75-L91

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedErrorSupport
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_NormalizedRun
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedErrorBridge
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
universe u v w
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Parameterized.instDecodedBridgeClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Parameterized.instDecodedBridgeClassicalDecidable

theorem QEC.Distillation.HH18Parameterized.decodedErrorBranch_traceError_le_two {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (error : PhysicalErrorWord m w) :
    outputTraceError (decodedErrorBranch h hdegree error) (idealLogicalTOutput m w) ≤ 2 := by sorry
