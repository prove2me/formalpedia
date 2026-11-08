-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_f256SourceInput_measurementDistance
-- name    : QEC.Distillation.Ngu24MultiplicativeCSS.f256SourceInput_measurementDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:39:27.457438+00:00
-- url     : https://prove2.me/theorems/4d936700-b13c-4059-8253-dbf959bdcbe3
-- title:
--   Ngu24 Multiplicative CSS: f256 Source Input measurement Distance
-- statement:
--   The concrete family satisfies the standard finite-qudit measurement-distance
--   predicate after the explicit coordinatewise computational-basis relabelling.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/NormalClosureDistance.lean#L112-L121
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/NormalClosureDistance.lean#L112-L121

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureInterpolation
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureInput
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CosetDetectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteAlphabetLocality
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureDistance
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24MultiplicativeCSS
open Coding Coding.AlgebraicGeometry Coding.AlgebraicGeometry.F256GarciaStichtenoth
open Semantics
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCSS._p2m_local_instance_5d3c569749_91

theorem QEC.Distillation.Ngu24MultiplicativeCSS.f256SourceInput_measurementDistance (i : ℕ) :
    QuditSubsystem.BPTMeasurementDistance
      ((f256SourceInput i).quantumCode.transport
        (FiniteAlphabet.registerUnitary F256 (f256SourceInput i).PivotComplement))
      ((f256GarciaStichtenothLength i + 4) / 5 - f256MultiplicationLogicalCount i) := by sorry
