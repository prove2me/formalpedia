-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolEnoughMass_add_decodedRetryPoolShortageMass
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolEnoughMass_add_decodedRetryPoolShortageMass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:05:48.345706+00:00
-- url     : https://prove2.me/theorems/742d28f9-25dd-486a-a864-9f5a75f8ed48
-- title:
--   HH18 Parameterized: decoded Retry Pool Enough Mass add decoded Retry Pool Shortage Mass
-- statement:
--   The pool's enough and shortage observed-history masses partition the
--   complete physical Born mass.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Core.lean#L181-L191
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Core.lean#L181-L191

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolEnoughMass_add_decodedRetryPoolShortageMass {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (attempts required : Nat)
    (rho : DensityOperator (tensorPowerCarrier (PhysicalRegister m w) attempts)) :
    decodedRetryPoolEnoughMass h hdegree attempts required rho +
        decodedRetryPoolShortageMass h hdegree attempts required rho = 1 := by sorry
