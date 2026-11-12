-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedErrorBranch_toOperator
-- name    : QEC.Distillation.HH18Parameterized.decodedErrorBranch_toOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:36:53.520186+00:00
-- url     : https://prove2.me/theorems/e9d3ed2f-5870-4238-aee6-513b64ff5788
-- title:
--   HH18 Parameterized: decoded Error Branch to Operator
-- statement:
--   The HH18 Parameterized construction uses the decoded Error Branch to Operator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedErrorBridge.lean#L63-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedErrorBridge.lean#L63-L71

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

theorem QEC.Distillation.HH18Parameterized.decodedErrorBranch_toOperator {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (error : PhysicalErrorWord m w) :
    (decodedErrorBranch h hdegree error).toOperator =
      decoderChannel h (errorBranchOperator h hdegree error) := by sorry
