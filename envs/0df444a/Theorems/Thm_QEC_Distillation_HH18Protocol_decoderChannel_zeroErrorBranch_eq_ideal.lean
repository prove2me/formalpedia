-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_decoderChannel_zeroErrorBranch_eq_ideal
-- name    : QEC.Distillation.HH18Protocol.decoderChannel_zeroErrorBranch_eq_ideal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:25:28.929588+00:00
-- url     : https://prove2.me/theorems/b924c720-eb69-40cc-95ab-13ca5e767469
-- title:
--   HH18 Protocol: decoder Channel zero Error Branch eq ideal
-- statement:
--   The total decoder applied to the error-free accepted physical branch is
--   the source-selected logical `T` density.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/DecodedErrorBridge.lean#L35-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/DecodedErrorBridge.lean#L35-L56

import Definitions.Def_QEC_Distillation_Core_FiniteDecodedTrace
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhysicalEndpoint
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Decoder
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_NormalizedRun
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_DecodedErrorBridge
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Protocol
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
universe u v w
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Protocol.instDecodedBridgeClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Protocol.instDecodedBridgeClassicalDecidable

theorem QEC.Distillation.HH18Protocol.decoderChannel_zeroErrorBranch_eq_ideal :
    decoderChannel
        (HH18SyndromeDecoding.errorBranchOperator (0 : PhysicalErrorWord)) =
      idealLogicalTOutput.toOperator := by sorry
