-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolOneQubitRecordDensity_toOperator
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolOneQubitRecordDensity_toOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:53:33.217481+00:00
-- url     : https://prove2.me/theorems/51e552e7-3551-44d0-aab3-da75d23319e3
-- title:
--   HH18 Parameterized: decoded Retry Pool One Qubit Record Density to Operator
-- statement:
--   The record density is the literal computational-basis mixture with the
--   actual clean and error weights.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Measurement.lean#L68-L103
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Measurement.lean#L68-L103

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Preparation
import Definitions.Def_QEC_Semantics_Instruments_Registers_ChannelProduct
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Measurement
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolOneQubitRecordDensity_toOperator
    (parameter : ErrorParameter) :
    (decodedRetryPoolOneQubitRecordDensity parameter).toOperator =
      (parameter.cleanWeight : Complex) •
          (InnerProductSpace.rankOne Complex
            (EuclideanSpace.basisFun (Fin 2) Complex 0)
            (EuclideanSpace.basisFun (Fin 2) Complex 0)).toLinearMap +
        (parameter.rate : Complex) •
          (InnerProductSpace.rankOne Complex
            (EuclideanSpace.basisFun (Fin 2) Complex 1)
            (EuclideanSpace.basisFun (Fin 2) Complex 1)).toLinearMap := by sorry
