-- Prove2me | Theorems.Thm_QEC_Distillation_Why24OneRoundProtocol_Why24LocalStochasticPreparation_why24LocalStochastic_tail_maxRate
-- name    : QEC.Distillation.Why24OneRoundProtocol.Why24LocalStochasticPreparation.why24LocalStochastic_tail_maxRate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:40:33.698019+00:00
-- url     : https://prove2.me/theorems/9ff82615-dfdf-4337-bc00-e53920c7ec6a
-- title:
--   Why24 Local Stochastic Preparation: why24 Local Stochastic tail max Rate
-- statement:
--   The per-location tail law implies the usual uniform local-stochastic
--   bound at the physical rate, without replacing the correlated preparation by
--   an IID distribution.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/ConstantOverheadProtocol/OneRound.lean#L175-L182
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/ConstantOverheadProtocol/OneRound.lean#L175-L182

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
open QEC.Distillation.Why24OneRoundProtocol.Why24LocalStochasticPreparation
variable {Location : Type} [Fintype Location] [DecidableEq Location]
variable {ideal : DensityOperator (Why24CCZRegister Location)}

theorem QEC.Distillation.Why24OneRoundProtocol.Why24LocalStochasticPreparation.why24LocalStochastic_tail_maxRate
    (preparation : Why24LocalStochasticPreparation Location ideal)
    (sites : Finset Location) :
    (∑ fault : Finset Location,
      if sites ⊆ fault then preparation.faultMass fault else 0) <=
        preparation.rate ^ sites.card := by sorry
