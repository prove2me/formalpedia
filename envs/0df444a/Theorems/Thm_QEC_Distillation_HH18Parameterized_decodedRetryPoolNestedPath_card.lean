-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolNestedPath_card
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolNestedPath_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:19:06.954988+00:00
-- url     : https://prove2.me/theorems/10316cc4-5d6d-462a-9268-a59f974dde40
-- title:
--   HH18 Parameterized: decoded Retry Pool Nested Path card
-- statement:
--   The physical nested path carrier has exactly the existing logical branch
--   count raised to its depth.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Paths/NestedPathRouting.lean#L69-L72
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Paths/NestedPathRouting.lean#L69-L72

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Regrouping
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathEnvelope
import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_Power
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_NestedPathRouting
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Semantics.FiniteInstrument
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolNestedPath_card (m w depth : Nat) :
    Fintype.card (nestedTensorPath (logicalOutputCount m w) depth) =
      logicalOutputCount m w ^ depth := by sorry
