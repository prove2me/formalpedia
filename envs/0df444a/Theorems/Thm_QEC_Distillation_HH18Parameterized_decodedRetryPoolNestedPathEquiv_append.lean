-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolNestedPathEquiv_append
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolNestedPathEquiv_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:39:35.906496+00:00
-- url     : https://prove2.me/theorems/3cf31bde-96e1-42f0-88cc-5ee48628e668
-- title:
--   HH18 Parameterized: decoded Retry Pool Nested Path Equiv append
-- statement:
--   Appending one finite tensor coordinate is exactly appending its logical
--   site to the corresponding routed output path.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Paths/NestedPathRouting.lean#L44-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Paths/NestedPathRouting.lean#L44-L65

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Regrouping
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathEnvelope
import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_Power
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_NestedPathRouting
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Semantics.FiniteInstrument
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolNestedPathEquiv_append
    (m w depth : Nat)
    (path : nestedTensorPath (logicalOutputCount m w) depth)
    (trial : Fin (logicalOutputCount m w)) :
    decodedRetryPoolNestedPathEquiv m w (depth + 1) (path, trial) =
      routedDepthOutputPathAppend m w depth
        (decodedRetryPoolNestedPathEquiv m w depth path)
        ((decodedRetryPoolLogicalSiteFinEquiv m w).symm trial) := by sorry
