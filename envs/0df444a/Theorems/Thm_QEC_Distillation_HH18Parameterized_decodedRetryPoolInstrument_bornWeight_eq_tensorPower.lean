-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolInstrument_bornWeight_eq_tensorPower
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolInstrument_bornWeight_eq_tensorPower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:02:13.202581+00:00
-- url     : https://prove2.me/theorems/1077dc5c-9569-4a23-ab62-749e11aaa0bc
-- title:
--   HH18 Parameterized: decoded Retry Pool Instrument born Weight eq tensor Power
-- statement:
--   The total selected-or-replacement stage preserves every actual decoded
--   observed-history Born mass.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Core.lean#L119-L129
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Core.lean#L119-L129

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolInstrument_bornWeight_eq_tensorPower {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (attempts required : Nat)
    (history : tensorPowerHistory DistillationOutcome attempts)
    (rho : DensityOperator (tensorPowerCarrier (PhysicalRegister m w) attempts)) :
    (decodedRetryPoolInstrument h hdegree attempts required).bornWeight
        ⟨history, PUnit.unit⟩ rho =
      ((decodedInstrument h hdegree).tensorPower attempts).bornWeight history rho := by sorry
