-- Prove2me | Theorems.Thm_QEC_Distillation_Why24OneRoundProtocol_f1024Why24OddAGDualDecoder_alwaysReturns
-- name    : QEC.Distillation.Why24OneRoundProtocol.f1024Why24OddAGDualDecoder_alwaysReturns
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:45:33.897949+00:00
-- url     : https://prove2.me/theorems/181df492-d428-4c02-8903-5f182089df81
-- title:
--   Why24 One Round Protocol: f1024 Why24 Odd AGDual Decoder always Returns
-- statement:
--   The decoder always returns a physical word.  On the solvable branch that
--   word is the literal constrained linear-system solution with the requested
--   intrinsic syndrome; otherwise the total fallback is zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/ConstantOverheadProtocol/OneRound.lean#L2293-L2316
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/ConstantOverheadProtocol/OneRound.lean#L2293-L2316

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

theorem QEC.Distillation.Why24OneRoundProtocol.f1024Why24OddAGDualDecoder_alwaysReturns (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r) :
    (∃ recovered : LinearMap.ker
        (why24DecoderLocatorProductLinearMap r
          (why24DecoderLocator r syndrome)),
      f1024Why24OddAGDualDecoder r syndrome = recovered.1 ∧
        f1024Why24OddZSyndromeMap r recovered.1 = syndrome) ∨
      (syndrome ∉ LinearMap.range
        (why24DecoderRecoverySyndromeMap r syndrome) ∧
        f1024Why24OddAGDualDecoder r syndrome = 0) := by sorry
