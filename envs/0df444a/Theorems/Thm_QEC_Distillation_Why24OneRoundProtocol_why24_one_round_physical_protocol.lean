-- Prove2me | Theorems.Thm_QEC_Distillation_Why24OneRoundProtocol_why24_one_round_physical_protocol
-- name    : QEC.Distillation.Why24OneRoundProtocol.why24_one_round_physical_protocol
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:43:42.893664+00:00
-- url     : https://prove2.me/theorems/feaf4a5c-7627-48c0-89b9-3f2b64f401a0
-- title:
--   Why24 One Round Protocol: why24 one round physical protocol
-- statement:
--   Complete finite WHY24 one-round handoff.  It exposes the actual shared
--   protocol, exact resource counts, deterministic success, and the correlated
--   local-stochastic output bound needed by the terminal asymptotic child.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/ConstantOverheadProtocol/OneRound.lean#L5794-L5817
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/ConstantOverheadProtocol/OneRound.lean#L5794-L5817

import Definitions.Def_QEC_Coding_QuditQubitConversion_ResourceCircuit
import Definitions.Def_QEC_Distillation_Core_FiniteDecodedTrace
import Definitions.Def_QEC_Distillation_Core_FiniteInstrumentBinaryRun
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_MagicResource
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_ConstantOverheadProtocol_AlgebraicGeometryFamily
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Semantics_Instruments_Sequential_Composition
import Definitions.Def_QEC_Semantics_Instruments_Registers_ProductDensity
import Definitions.Def_QEC_Semantics_Instruments_Registers_Marginal
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Channels_Instrument
import Definitions.Def_QEC_Distillation_ConstantOverheadProtocol_OneRound
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Why24OneRoundProtocol
open QEC.Coding
open QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
open QEC.Distillation
open QEC.Distillation.Why24AGFamily
open QEC.Distillation.KT19PrimeQuditCSS
open QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS
open QEC.Distillation.Why24WeightedTriorthogonalCSS
open QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix
open QEC.Semantics
open scoped BigOperators ComplexOrder
attribute [local instance]
  QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype
attribute [local instance] QEC.Distillation.Why24OneRoundProtocol.instWhy24OneRoundClassicalDecidable
attribute [local instance] QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype QEC.Distillation.Why24OneRoundProtocol.instWhy24OneRoundClassicalDecidable
open QEC.Distillation.OneQubitMagic
attribute [local instance 2000] QEC.Distillation.Why24OneRoundProtocol.why24DecoderDirectConstantAlgebra
attribute [local instance 2000] QEC.Distillation.Why24OneRoundProtocol.why24DecoderDirectConstantScalarTower
attribute [local instance 2000] QEC.Distillation.Why24OneRoundProtocol.why24DecoderDirectConstantAlgebra QEC.Distillation.Why24OneRoundProtocol.why24DecoderDirectConstantScalarTower

theorem QEC.Distillation.Why24OneRoundProtocol.why24_one_round_physical_protocol (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))) :
    let protocol :=
      why24OneRoundMagicStateDistillationProtocol r preparation
    protocol.run = why24OneRoundRun r preparation ∧
      protocol.inputErrorModel = InputErrorModel.localStochastic
        (why24LocalStochasticInputErrorModel preparation) ∧
      protocol.behavior = .activeCorrection (QuantumChannel.id _) ∧
      protocol.run.resourceCount = 70 * f1024Why24OddLength r ∧
      why24OneRoundOutputCount r = f1024Why24OddDimension r ∧
      protocol.run.successProbability = 1 ∧
      protocol.successfulOutputError ≤
        (Nat.choose (f1024Why24OddLength r)
          (f1024Why24OddDecodingRadius r + 1) : Real) *
          (70 * preparation.rate) ^
            (f1024Why24OddDecodingRadius r + 1) := by sorry
