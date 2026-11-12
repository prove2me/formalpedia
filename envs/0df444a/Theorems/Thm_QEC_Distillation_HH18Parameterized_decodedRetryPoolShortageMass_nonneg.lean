-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolShortageMass_nonneg
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolShortageMass_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:04:05.343917+00:00
-- url     : https://prove2.me/theorems/1b6fbf77-da6f-4a26-a480-e14fb7806429
-- title:
--   HH18 Parameterized: decoded Retry Pool Shortage Mass nonneg
-- statement:
--   The shortage-event mass is nonnegative because it is a finite sum of
--   physical Born weights.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Core.lean#L169-L177
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Core.lean#L169-L177

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolShortageMass_nonneg {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (attempts required : Nat)
    (rho : DensityOperator (tensorPowerCarrier (PhysicalRegister m w) attempts)) :
    0 ≤ decodedRetryPoolShortageMass h hdegree attempts required rho := by sorry
