-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolQubitTensorPowerBitstringEquiv_symm_at
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolQubitTensorPowerBitstringEquiv_symm_at
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:23:57.923359+00:00
-- url     : https://prove2.me/theorems/5e7a56da-fe49-4687-b8a0-c2f5157f1209
-- title:
--   HH18 Parameterized: decoded Retry Pool Qubit Tensor Power Bitstring Equiv symm at
-- statement:
--   An inverse transported history stores exactly the original register bit
--   at the corresponding canonically enumerated site.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Preparation.lean#L121-L132
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Preparation.lean#L121-L132

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolQubitTensorPowerBitstringEquiv_symm_at
    (ι : Type) [Fintype ι] (bits : Bitstring ι)
    (coordinate : Fin (Fintype.card ι)) :
    tensorPowerHistoryAt (Fin 2) (Fintype.card ι)
        ((decodedRetryPoolQubitTensorPowerBitstringEquiv ι).symm bits) coordinate =
      bits ((Fintype.equivFin ι).symm coordinate) := by sorry
