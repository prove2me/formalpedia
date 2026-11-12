-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolInstrument_complete
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolInstrument_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:01:56.24587+00:00
-- url     : https://prove2.me/theorems/a7ae9b1e-c867-4450-acb7-4c7ec4e04030
-- title:
--   HH18 Parameterized: decoded Retry Pool Instrument complete
-- statement:
--   Completeness of the actual retry-pool Kraus family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Core.lean#L108-L115
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Core.lean#L108-L115

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedInstrument
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Core
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Parameterized.instDecodedRetryPoolClassicalDecidable

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolInstrument_complete {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (attempts required : Nat) :
    (decodedRetryPoolInstrument h hdegree attempts required).kraus.Complete := by sorry
