-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decoderChannel_zeroErrorBranch_eq_ideal
-- name    : QEC.Distillation.HH18Parameterized.decoderChannel_zeroErrorBranch_eq_ideal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:07:04.859267+00:00
-- url     : https://prove2.me/theorems/9aa5a6ae-1e89-42f8-a173-770b0c771b07
-- title:
--   HH18 Parameterized: decoder Channel zero Error Branch eq ideal
-- statement:
--   The total decoder maps the error-free physical branch to the actual
--   parameterized logical-`T` target.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedErrorBridge.lean#L34-L53
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedErrorBridge.lean#L34-L53

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

theorem QEC.Distillation.HH18Parameterized.decoderChannel_zeroErrorBranch_eq_ideal {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m) :
    decoderChannel h (errorBranchOperator h hdegree (0 : PhysicalErrorWord m w)) =
      (idealLogicalTOutput m w).toOperator := by sorry
