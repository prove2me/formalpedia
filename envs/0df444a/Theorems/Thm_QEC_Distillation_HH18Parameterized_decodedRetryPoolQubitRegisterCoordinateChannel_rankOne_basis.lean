-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolQubitRegisterCoordinateChannel_rankOne_basis
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolQubitRegisterCoordinateChannel_rankOne_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:24:04.630612+00:00
-- url     : https://prove2.me/theorems/8e7b535a-fd74-4f41-a2e6-c1ae60ce53c0
-- title:
--   HH18 Parameterized: decoded Retry Pool Qubit Register Coordinate Channel rank One basis
-- statement:
--   The canonical coordinate channel contracts every discarded
--   computational coordinate and retains the nominated one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Preparation.lean#L136-L160
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Preparation.lean#L136-L160

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Routing
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DepthTwoRouting
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_Basis
import Definitions.Def_QEC_Semantics_Instruments_Registers_Marginal
import Definitions.Def_QEC_Semantics_Channels_Instrument
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Preparation
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm

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
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolQubitRegisterCoordinateChannel_rankOne_basis
    (ι : Type) [Fintype ι] [DecidableEq ι] (site : ι)
    (left right : Bitstring ι) :
    decodedRetryPoolQubitRegisterCoordinateChannel ι site
        (InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun (Bitstring ι) Complex left)
          (EuclideanSpace.basisFun (Bitstring ι) Complex right)).toLinearMap =
      (∏ coordinate : Fin (Fintype.card ι),
          if coordinate = Fintype.equivFin ι site then 1
          else inner Complex
            (EuclideanSpace.basisFun (Fin 2) Complex
              (right ((Fintype.equivFin ι).symm coordinate)))
            (EuclideanSpace.basisFun (Fin 2) Complex
              (left ((Fintype.equivFin ι).symm coordinate)))) •
        (InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun (Fin 2) Complex (left site))
          (EuclideanSpace.basisFun (Fin 2) Complex (right site))).toLinearMap := by sorry
